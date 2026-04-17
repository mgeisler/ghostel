;;; ghostel-compile.el --- Compilation integration for ghostel -*- lexical-binding: t; -*-

;; Author: Daniel Kraus <daniel@kraus.my>
;; Keywords: processes, tools, convenience
;; Package-Requires: ((emacs "28.1"))
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:

;; Run `compile'-style shell commands inside a ghostel terminal
;; buffer.  Unlike \\[compile] (which runs commands through comint),
;; `ghostel-compile' runs them in a real TTY via ghostel so programs
;; that detect a terminal (progress bars, colours, curses tools)
;; behave as they would in an interactive shell.
;;
;; Each `ghostel-compile' invocation spawns a fresh process via
;; `shell-file-name -c COMMAND' through a PTY owned by the ghostel
;; renderer — no interactive shell sits between the command and the
;; user.  Multi-line scripts are passed verbatim to the shell.  No
;; OSC 133 / shell integration is required; completion is detected
;; by the process sentinel, which delivers the real exit status.
;;
;; The buffer mimics `compilation-mode': a "Compilation started at"
;; header, a "Compilation finished at ..., duration ..." footer, and
;; the same `mode-line-process' run/exit faces.
;;
;; When the command finishes, the renderer is torn down and the
;; buffer's major mode is switched to `ghostel-compile-view-mode'
;; (derived from `compilation-mode').  At that point the buffer is a
;; regular, read-only Emacs buffer with standard error highlighting
;; and `next-error' navigation.  It will not return to an interactive
;; ghostel terminal — a recompile (`g', `M-x ghostel-recompile')
;; discards it and starts fresh in the original `default-directory'.
;;
;; Enable `ghostel-compile-global-mode' to route *all* `compile',
;; `recompile', `project-compile', ... calls through ghostel.  It
;; advises `compilation-start' so every caller benefits without any
;; further configuration.  `grep-mode' (and comint mode) falls through
;; to the stock implementation.
;;
;; Standard `compile' options honoured:
;;   `compile-command' / `compile-history' (shared with \\[compile])
;;   `compilation-read-command'
;;   `compilation-ask-about-save'
;;   `compilation-auto-jump-to-first-error'
;;   `compilation-finish-functions' (runs alongside
;;     `ghostel-compile-finish-functions')
;;   `compilation-scroll-output' (effectively always on)
;;
;; Keys in the finished buffer:
;;   g           — ghostel-recompile
;;   n / p       — compilation-next-error / -previous-error (no auto-open)
;;   RET         — compile-goto-error (open the source)
;;   M-g n / M-g p — standard `next-error' / `previous-error'

;;; Code:

(require 'ghostel)
(require 'compile)


;;; Customization

(defgroup ghostel-compile nil
  "Run `compile'-style commands in a ghostel terminal."
  :group 'ghostel)

(defcustom ghostel-compile-buffer-name "*ghostel-compile*"
  "Buffer name used by `ghostel-compile'."
  :type 'string)

(defcustom ghostel-compile-finished-major-mode 'ghostel-compile-view-mode
  "Major mode to switch to after a `ghostel-compile' run finishes.

The default `ghostel-compile-view-mode' derives from `compilation-mode',
making the buffer a regular read-only Emacs buffer with `next-error'
navigation and colored error text.

Set to nil to skip the major-mode switch and leave the buffer in
`ghostel-mode'.  Either way, finalization always tears down the live
process and ghostel rendering — the buffer never returns to an
interactive terminal."
  :type '(choice (const :tag "Compilation view (default)" ghostel-compile-view-mode)
                 (const :tag "Don't switch" nil)
                 (function :tag "Custom major mode")))

(defcustom ghostel-compile-debug nil
  "When non-nil, log `ghostel-compile' lifecycle events to *Messages*.
Useful for diagnosing wrong exit codes or missed events."
  :type 'boolean)

(defcustom ghostel-compile-finish-functions nil
  "Functions to call when a `ghostel-compile' command finishes.
Each function receives two arguments: the compilation buffer and a
status message string (e.g. \"finished\\n\" or
\"exited abnormally with code 2\\n\"), matching the convention of
`compilation-finish-functions'.

`compilation-finish-functions' is also run with the same arguments."
  :type 'hook)


;;; Internal variables

(defvar-local ghostel-compile--command nil
  "The command most recently launched by `ghostel-compile' here.")

(defvar-local ghostel-compile--scan-marker nil
  "Marker at the buffer position where the current command's output began.")

(defvar-local ghostel-compile--last-exit nil
  "Exit status of the most recent `ghostel-compile' command.")

(defvar-local ghostel-compile--start-time nil
  "`current-time' when the most recent command was launched.")

(defvar-local ghostel-compile--directory nil
  "`default-directory' captured at `ghostel-compile' invocation time.
Used by `ghostel-recompile' so the command re-runs in the same
directory regardless of where the user is when they press `g'.")

(defvar-local ghostel-compile--header-marker nil
  "Marker at the end of the inserted compilation header.")

(defvar-local ghostel-compile--footer-marker nil
  "Marker at the start of the inserted compilation footer.")

(defvar-local ghostel-compile--finalized nil
  "Non-nil once the sentinel has finalized this run.
Second-chance guard: if the sentinel fires twice (process exit
followed by teardown) we only run the heavy finalize path once.")

(defvar ghostel-compile-mode)          ; forward decl for `ghostel-compile--start'

(defvar-local ghostel-compile--owns-compilation-minor-mode nil
  "Non-nil if `ghostel-compile-mode' enabled `compilation-minor-mode'.
Tracked so disabling our mode only turns off `compilation-minor-mode'
when we were the ones who turned it on — never when the user (or
some other minor mode) had it enabled independently.")

(defvar ghostel-compile-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "g") #'ghostel-recompile)
    map)
  "Keymap for `ghostel-compile-mode'.
Shadows `compilation-minor-mode-map' bindings that clash.")

(defvar ghostel-compile-view-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map compilation-mode-map)
    ;; `n'/`p' navigate within the compile buffer only (no auto-open).
    ;; RET / mouse-2 still jump to the source like in `compilation-mode'.
    (define-key map "n" #'compilation-next-error)
    (define-key map "p" #'compilation-previous-error)
    (define-key map "g" #'ghostel-recompile)
    map)
  "Keymap for `ghostel-compile-view-mode'.
Inherits from `compilation-mode-map'; rebinds `n'/`p' to
`compilation-next-error' / `compilation-previous-error' so they
just move point through errors without opening the source file
in another window.  `g' runs `ghostel-recompile' instead of
`recompile'.  RET still opens the error like in `compilation-mode'.")


;;; Helpers

(define-derived-mode ghostel-compile-view-mode
  compilation-mode "Compilation"
  "Major mode for a finished `ghostel-compile' buffer.

A regular, read-only Emacs buffer.  `g' re-runs the command via
`ghostel-recompile', `n'/`p' walk errors in the buffer (without
opening files), RET jumps to the source.  The live process and
ghostel rendering have been torn down; the buffer will not return
to a ghostel terminal."
  :group 'ghostel-compile
  ;; Make sure our keymap actually parents `compilation-mode-map' even
  ;; if it was created earlier — `define-derived-mode' won't reset an
  ;; already-set parent.
  (set-keymap-parent ghostel-compile-view-mode-map compilation-mode-map)
  (setq-local next-error-function #'compilation-next-error-function)
  ;; Make sure point lands at the top after a successful recompile (and
  ;; that future input doesn't inherit ghostel's terminal-style behaviour).
  (setq-local window-point-insertion-type nil))

(defun ghostel-compile--format-duration (seconds)
  "Format SECONDS (float) as a compilation-style duration string.
Matches the format used by `M-x compile'."
  (cond
   ((< seconds 10) (format "%.2f s" seconds))
   ((< seconds 60) (format "%.1f s" seconds))
   (t              (format-seconds "%h:%02m:%02s" seconds))))

(defun ghostel-compile--status-message (exit)
  "Return the compile-style status message string for EXIT status."
  (cond
   ((and (numberp exit) (= exit 0)) "finished\n")
   ((numberp exit) (format "exited abnormally with code %d\n" exit))
   (t              "finished\n")))

(defun ghostel-compile--clear-markers ()
  "Reset header/footer markers."
  (when (markerp ghostel-compile--header-marker)
    (set-marker ghostel-compile--header-marker nil))
  (when (markerp ghostel-compile--footer-marker)
    (set-marker ghostel-compile--footer-marker nil))
  (setq ghostel-compile--header-marker nil
        ghostel-compile--footer-marker nil))

(defun ghostel-compile--header-text (command start-time)
  "Return the header string for COMMAND started at START-TIME.
Plain text, matching the `M-x compile' header format."
  (format "-*- mode: ghostel-compile -*-\nCompilation started at %s\n\n%s\n"
          (substring (current-time-string start-time) 0 19)
          command))

(defun ghostel-compile--footer-text (exit start-time end-time)
  "Return the footer string for EXIT between START-TIME and END-TIME.
Plain text, matching the `M-x compile' footer format."
  (let* ((duration (float-time (time-subtract end-time start-time)))
         (ts (substring (current-time-string end-time) 0 19))
         (status-word (cond
                       ((and (numberp exit) (= exit 0)) "finished")
                       ((numberp exit)
                        (format "exited abnormally with code %d" exit))
                       (t "finished"))))
    (format "Compilation %s at %s, duration %s\n"
            status-word ts (ghostel-compile--format-duration duration))))

(defun ghostel-compile--set-mode-line-running ()
  "Set `mode-line-process' to the running indicator."
  (setq mode-line-process
        (list '(:propertize ":run" face compilation-mode-line-run)
              'compilation-mode-line-errors))
  (force-mode-line-update))

(defun ghostel-compile--set-mode-line-exit (exit)
  "Set `mode-line-process' to reflect the terminal EXIT status."
  (let* ((ok (and (numberp exit) (= exit 0)))
         (face (if ok 'compilation-mode-line-exit 'compilation-mode-line-fail))
         (text (format ":exit [%s]" (if (numberp exit) exit "?"))))
    (setq mode-line-process
          (list (propertize text 'face face)
                'compilation-mode-line-errors))
    (force-mode-line-update)))

(defun ghostel-compile--auto-jump (buffer)
  "Jump to the first error in BUFFER if `compilation-auto-jump-to-first-error'."
  (when (and compilation-auto-jump-to-first-error
             (buffer-live-p buffer))
    (with-current-buffer buffer
      (let ((next-error-last-buffer buffer))
        (condition-case _
            (first-error)
          (error nil))))))

(defun ghostel-compile--teardown-terminal ()
  "Tear down the live process and ghostel renderer in the current buffer.
Replaces the sentinel and filter with no-ops before deleting the
process so the default sentinel can't write \"Process NAME killed\"
into our buffer."
  (when (and (bound-and-true-p ghostel--process)
             (process-live-p ghostel--process))
    (set-process-sentinel ghostel--process #'ignore)
    (set-process-filter ghostel--process #'ignore)
    (set-process-query-on-exit-flag ghostel--process nil)
    (delete-process ghostel--process)
    (setq ghostel--process nil))
  (when (bound-and-true-p ghostel--redraw-timer)
    (cancel-timer ghostel--redraw-timer)
    (setq ghostel--redraw-timer nil))
  (when (bound-and-true-p ghostel--input-timer)
    (cancel-timer ghostel--input-timer)
    (setq ghostel--input-timer nil)))

(defun ghostel-compile--trim-trailing-blanks (start)
  "Delete trailing whitespace-only content in START..(point-max).
The ghostel renderer commits the full terminal grid to the buffer,
so a short command (`echo test') leaves ~24 rows of trailing
spaces and newlines that would otherwise wedge the footer far
below the real output.  Find the last non-whitespace position in
the scan region and delete everything after it, leaving a single
trailing newline so the footer's leading `\\n' produces a blank
separator line — matching `M-x compile's output format."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n" start)
    (when (< (point) (point-max))
      (delete-region (point) (point-max))
      (insert "\n"))))

(defun ghostel-compile--finalize (buffer exit end-time)
  "Insert header/footer, parse errors, switch major mode for BUFFER.
EXIT is the command exit status; END-TIME its completion time.
Safe to call more than once — second and later calls are no-ops
thanks to `ghostel-compile--finalized'.

Switches the buffer's major mode to
`ghostel-compile-finished-major-mode' (by default
`ghostel-compile-view-mode') so the buffer becomes a regular,
read-only Emacs buffer that can never transition back to
interactive terminal mode.

Header and footer are inserted as plain buffer text (matching
`M-x compile') rather than overlays, so cursor motion behaves the
same as in any compilation buffer."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (unless ghostel-compile--finalized
        (setq ghostel-compile--finalized t)
        (let* ((start (and ghostel-compile--scan-marker
                           (marker-position ghostel-compile--scan-marker)))
               (start-time ghostel-compile--start-time)
               (command ghostel-compile--command)
               (directory ghostel-compile--directory)
               (header (ghostel-compile--header-text command start-time))
               (footer (ghostel-compile--footer-text exit start-time end-time))
               (inhibit-read-only t))
          (setq ghostel-compile--last-exit exit)
          (when ghostel-compile-debug
            (message "ghostel-compile: finalizing exit=%S buffer=%S"
                     exit (buffer-name buffer)))
          (when start
            (ghostel-compile--trim-trailing-blanks start))
          (ghostel-compile--clear-markers)
          (ghostel-compile--teardown-terminal)
          ;; Switch major mode now that the process is dead.  Preserve state
          ;; that `kill-all-local-variables' would otherwise wipe.
          (let ((saved-command command)
                (saved-start-time start-time)
                (saved-directory directory))
            (when ghostel-compile-finished-major-mode
              (funcall ghostel-compile-finished-major-mode))
            (setq-local ghostel-compile--command saved-command
                        ghostel-compile--directory saved-directory
                        ghostel-compile--start-time saved-start-time
                        ghostel-compile--last-exit exit
                        ghostel-compile--finalized t)
            ;; Pin the buffer's `default-directory' to the directory the
            ;; user invoked `ghostel-compile' from, so it doesn't drift if
            ;; the command happened to `cd' elsewhere during the run.
            (when saved-directory
              (setq default-directory saved-directory)))
          ;; Anchor header at the start of THIS run's output, not at
          ;; point-min — when older output remains in the buffer (callers
          ;; that reuse buffers), the header should still bracket the
          ;; right region.  Track the resulting parse-start so jit-lock
          ;; doesn't pick up stale matches above the run.
          (let* ((inhibit-read-only t)
                 (header-anchor (or start (point-min)))
                 (parse-start (copy-marker header-anchor)))
            (save-excursion
              (goto-char header-anchor)
              (insert header)
              (setq ghostel-compile--header-marker (point-marker))
              (set-marker-insertion-type ghostel-compile--header-marker nil))
            (save-excursion
              (goto-char (point-max))
              (unless (or (= (point) (point-min)) (bolp))
                (insert "\n"))
              (setq ghostel-compile--footer-marker (point-marker))
              (set-marker-insertion-type ghostel-compile--footer-marker nil)
              (insert footer))
            (save-excursion
              (save-restriction
                (widen)
                (setq-local compilation--parsed (copy-marker parse-start))
                (condition-case err
                    (compilation--ensure-parse (point-max))
                  (error
                   (message "ghostel-compile: error scanning output: %s"
                            (error-message-string err)))))))
          (goto-char (point-max))
          (dolist (win (get-buffer-window-list buffer nil t))
            (set-window-point win (point-max))
            (with-selected-window win (recenter -1))))
        (ghostel-compile--set-mode-line-exit exit)
        (setq next-error-last-buffer buffer)
        (ghostel-compile--auto-jump buffer)
        (let ((msg (ghostel-compile--status-message exit)))
          (run-hook-with-args 'compilation-finish-functions buffer msg)
          (run-hook-with-args 'ghostel-compile-finish-functions buffer msg))))))


;;; Spawning

(defun ghostel-compile--sentinel (process _event)
  "Sentinel for the compile PROCESS: finalize the buffer on exit."
  (when (memq (process-status process) '(exit signal))
    (let ((buffer (process-buffer process))
          (exit (process-exit-status process)))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when ghostel-compile-debug
            (message "ghostel-compile: sentinel exit=%S status=%S"
                     exit (process-status process)))
          ;; Flush pending bytes to the VT parser, then cancel any
          ;; scheduled redraw and commit the current terminal state to
          ;; the buffer synchronously.  Without this, a short-lived
          ;; command (`echo`, `false`, `exit 7`) finishes before the
          ;; ~16 ms redraw timer fires and its output is lost when
          ;; `--teardown-terminal' destroys the renderer.
          (when ghostel--term
            (ghostel--flush-pending-output)
            (when ghostel--redraw-timer
              (cancel-timer ghostel--redraw-timer)
              (setq ghostel--redraw-timer nil))
            (ghostel--delayed-redraw buffer))
          (setq compilation-in-progress
                (delq process compilation-in-progress))
          (when (fboundp 'compilation--update-in-progress-mode-line)
            (compilation--update-in-progress-mode-line))
          (ghostel-compile--finalize buffer exit (current-time)))))))

(defun ghostel-compile--stty-flags ()
  "Return the `stty' flags used to initialize the compile PTY.
Matches what `ghostel--spawn-pty' uses for generic (non-shell)
programs, but with `echo' off so we don't render an echo of the
command (which users already see in the header)."
  "erase '^?' iutf8 -ixon -echo")

(defun ghostel-compile--spawn (command buffer height width)
  "Spawn COMMAND in BUFFER via a PTY sized HEIGHT rows by WIDTH columns.
Installs `ghostel--filter' and `ghostel-compile--sentinel'.  Returns
the process.

COMMAND is passed verbatim to `shell-file-name' via
`shell-command-switch', so multi-line scripts and shell
metacharacters are handled the same way `M-x compile' handles
them.  `/bin/sh' is used only to set PTY attributes (stty) before
exec'ing the user's shell."
  (let* ((shell shell-file-name)
         (switch shell-command-switch)
         (wrapper
          (list "/bin/sh" "-c"
                (concat
                 "stty " (ghostel-compile--stty-flags)
                 (format " rows %d columns %d" height width)
                 " 2>/dev/null; "
                 "exec "
                 (shell-quote-argument shell) " "
                 (shell-quote-argument switch) " "
                 (shell-quote-argument command))))
         (process-environment
          (append compilation-environment
                  (list (format "INSIDE_EMACS=%s,compile" emacs-version)
                        "TERM=xterm-256color"
                        "COLORTERM=truecolor"
                        ;; Defeat pagers (git grep, etc.).
                        "PAGER=")
                  (copy-sequence process-environment)))
         (proc (make-process
                :name "ghostel-compile"
                :buffer buffer
                :command wrapper
                :connection-type 'pty
                :file-handler (file-remote-p default-directory)
                :filter #'ghostel--filter
                :sentinel #'ghostel-compile--sentinel)))
    (set-process-coding-system proc 'binary 'binary)
    (set-process-window-size proc height width)
    (when compilation-always-kill
      (set-process-query-on-exit-flag proc nil))
    (process-put proc 'adjust-window-size-function
                 #'ghostel--window-adjust-process-window-size)
    proc))


;;; Buffer management

(defun ghostel-compile--prepare-buffer (name dir)
  "Return a fresh ghostel buffer named NAME rooted at DIR.
If a buffer with NAME already exists, kill it (after interrupting
any running process) so each run starts clean."
  (let ((existing (get-buffer name)))
    (when existing
      (with-current-buffer existing
        (let ((proc (bound-and-true-p ghostel--process)))
          (when (process-live-p proc)
            (if (or (eq (process-query-on-exit-flag proc) nil)
                    compilation-always-kill
                    (yes-or-no-p
                     (format "A %s process is running; kill it? "
                             (buffer-name existing))))
                (condition-case nil
                    (progn
                      (set-process-sentinel proc #'ignore)
                      (interrupt-process proc)
                      (sit-for 0.1)
                      (delete-process proc))
                  (error nil))
              (error "Cannot have two processes in `%s' at once"
                     (buffer-name existing))))))
      (let ((kill-buffer-query-functions nil))
        (kill-buffer existing))))
  (ghostel--load-module t)
  (let ((buffer (get-buffer-create name)))
    (with-current-buffer buffer
      (setq-local default-directory dir))
    (ghostel--init-buffer buffer)
    ;; `ghostel--init-buffer' starts a shell — we don't want one.  Tear it
    ;; down so the compile spawn can attach a fresh process to the same
    ;; ghostel renderer.
    (with-current-buffer buffer
      (when (and (bound-and-true-p ghostel--process)
                 (process-live-p ghostel--process))
        (set-process-sentinel ghostel--process #'ignore)
        (set-process-filter ghostel--process #'ignore)
        (set-process-query-on-exit-flag ghostel--process nil)
        (delete-process ghostel--process)
        (setq ghostel--process nil))
      (let ((inhibit-read-only t))
        (erase-buffer))
      ;; The init-started shell produced no output yet (we killed it
      ;; before it wrote anything), but reset any pending bytes anyway.
      (setq ghostel--pending-output nil)
      (when (bound-and-true-p ghostel--redraw-timer)
        (cancel-timer ghostel--redraw-timer)
        (setq ghostel--redraw-timer nil))
      (when (bound-and-true-p ghostel--input-timer)
        (cancel-timer ghostel--input-timer)
        (setq ghostel--input-timer nil)))
    buffer))


;;; Entry points

(defun ghostel-compile--start (command buffer-name dir)
  "Run COMMAND in BUFFER-NAME from DIR and return the buffer.
Creates or resets the buffer, spawns COMMAND via `shell-file-name',
and displays the buffer.  Used by both `ghostel-compile' and the
`compilation-start' advice installed by `ghostel-compile-global-mode'."
  (unless (and command (not (string-blank-p command)))
    (user-error "Empty compile command"))
  (save-some-buffers (not compilation-ask-about-save)
                     compilation-save-buffers-predicate)
  (let* ((buffer (ghostel-compile--prepare-buffer buffer-name dir))
         (outwin (display-buffer buffer '(nil (allow-no-window . t)))))
    (with-current-buffer buffer
      (unless ghostel-compile-mode
        (ghostel-compile-mode 1))
      (ghostel-compile--clear-markers)
      (setq ghostel-compile--command command
            ghostel-compile--directory dir
            ghostel-compile--start-time (current-time)
            ghostel-compile--last-exit nil
            ghostel-compile--finalized nil
            ghostel-compile--scan-marker (copy-marker (point-max)))
      (ghostel-compile--set-mode-line-running)
      (let* ((height (max 1 (if outwin
                                (window-body-height outwin)
                              (window-body-height))))
             (width (max 1 (if outwin
                               (window-body-width outwin)
                             (window-max-chars-per-line))))
             (proc (ghostel-compile--spawn command buffer height width)))
        (push proc compilation-in-progress)
        (when (fboundp 'compilation--update-in-progress-mode-line)
          (compilation--update-in-progress-mode-line))
        (setq next-error-last-buffer buffer)
        (run-hook-with-args 'compilation-start-hook proc)))
    buffer))

;;;###autoload
(defun ghostel-compile (command)
  "Run COMMAND in a ghostel terminal with compilation integration.

Like \\[compile], but uses a ghostel buffer so programs that require
a real TTY work correctly.  The buffer gets a compilation-mode-like
header and footer, and when the command finishes the major mode is
switched to `ghostel-compile-finished-major-mode' (by default
`ghostel-compile-view-mode', derived from `compilation-mode').
Error locations become available through `next-error'.

COMMAND is passed verbatim to `shell-file-name -c', so multi-line
scripts work exactly as in \\[shell-command].  No shell-integration
setup is required — the process sentinel reports the real exit
status.

Output always scrolls as it arrives (equivalent to
`compilation-scroll-output' being non-nil).  `compilation-ask-about-save'
and `compilation-auto-jump-to-first-error' are honoured.  The command
default and history are shared with \\[compile] via `compile-command'
and `compile-history'."
  (interactive
   (list
    (let ((default (eval compile-command t)))
      (if (or compilation-read-command current-prefix-arg)
          (read-shell-command "Ghostel compile: " default
                              (if (equal (car compile-history) default)
                                  '(compile-history . 1)
                                'compile-history))
        default))))
  (unless (equal command (eval compile-command t))
    (setq compile-command command))
  (ghostel-compile--start command ghostel-compile-buffer-name default-directory))

(defun ghostel-recompile (&optional edit-command)
  "Re-run the last `ghostel-compile' command in its original directory.
If EDIT-COMMAND is non-nil, prompt for the command so the user can
edit it before running — interactively this is triggered by a
prefix arg, matching the convention of \\[recompile].

Falls back to `compile-command' (and the current `default-directory')
when no ghostel compile has run yet."
  (interactive "P")
  (let* ((buf (get-buffer ghostel-compile-buffer-name))
         (cmd (or (and (buffer-live-p buf)
                       (buffer-local-value 'ghostel-compile--command buf))
                  (eval compile-command t)))
         (dir (or (and (buffer-live-p buf)
                       (buffer-local-value 'ghostel-compile--directory buf))
                  default-directory)))
    (unless (and cmd (not (string-blank-p cmd)))
      (user-error "No previous `ghostel-compile' command to re-run"))
    (when edit-command
      (setq cmd (read-shell-command
                 "Ghostel compile: " cmd
                 (if (equal (car compile-history) cmd)
                     '(compile-history . 1)
                   'compile-history)))
      (unless (equal cmd (eval compile-command t))
        (setq compile-command cmd)))
    (let ((default-directory dir))
      (ghostel-compile cmd))))


;;; ghostel-compile-mode (per-buffer)

(define-minor-mode ghostel-compile-mode
  "Minor mode: mark a ghostel buffer as a `ghostel-compile' buffer.

Enables `compilation-minor-mode' so `next-error' works and binds
\\<ghostel-compile-mode-map>\\[ghostel-recompile] to re-run the last
command.  `ghostel-compile' enables this automatically; you rarely
need to turn it on by hand."
  :lighter " gh-compile"
  :keymap ghostel-compile-mode-map
  (cond
   (ghostel-compile-mode
    (unless (derived-mode-p 'ghostel-mode)
      (setq ghostel-compile-mode nil)
      (user-error "`ghostel-compile-mode' can only be enabled in a ghostel buffer"))
    (setq ghostel-compile--owns-compilation-minor-mode
          (not (bound-and-true-p compilation-minor-mode)))
    (compilation-minor-mode 1)
    (setq-local next-error-function #'compilation-next-error-function)
    (setq-local minor-mode-overriding-map-alist
                (cons (cons 'ghostel-compile-mode ghostel-compile-mode-map)
                      (assq-delete-all
                       'ghostel-compile-mode
                       minor-mode-overriding-map-alist))))
   (t
    (setq-local minor-mode-overriding-map-alist
                (assq-delete-all
                 'ghostel-compile-mode
                 minor-mode-overriding-map-alist))
    (when (and ghostel-compile--owns-compilation-minor-mode
               (bound-and-true-p compilation-minor-mode))
      (compilation-minor-mode -1)
      (kill-local-variable 'next-error-function))
    (setq ghostel-compile--owns-compilation-minor-mode nil))))


;;; ghostel-compile-global-mode — opt-in: advise compilation-start

(defcustom ghostel-compile-global-mode-excluded-modes '(grep-mode)
  "Modes for which `ghostel-compile-global-mode' falls through to stock `compile'.
`grep-mode' is excluded by default because it has its own output
parsing and window-management conventions that don't fit a TTY.
Add your own compile-mode subclass to this list if you need to
opt a specific caller out."
  :type '(repeat symbol))

(defun ghostel-compile--compilation-start-advice
    (orig-fn command &optional mode name-function highlight-regexp continue)
  "Around advice for `compilation-start': route COMMAND through ghostel.
Falls back to ORIG-FN (with COMMAND, MODE, NAME-FUNCTION,
HIGHLIGHT-REGEXP, CONTINUE unchanged) when MODE is in
`ghostel-compile-global-mode-excluded-modes', or when MODE is t
\(which asks for a comint buffer — not supported).  Otherwise
routes COMMAND through `ghostel-compile--start', honouring
NAME-FUNCTION for the buffer name and HIGHLIGHT-REGEXP for error
highlighting.  CONTINUE is accepted but not supported — the
buffer is always replaced on each run."
  (if (or (eq mode t)
          (memq mode ghostel-compile-global-mode-excluded-modes))
      (funcall orig-fn command mode name-function highlight-regexp continue)
    (let* ((actual-mode (or mode 'compilation-mode))
           (name-of-mode
            (replace-regexp-in-string "-mode\\'" ""
                                      (symbol-name actual-mode)))
           (buf-name (compilation-buffer-name
                      name-of-mode actual-mode name-function))
           (buffer (ghostel-compile--start command buf-name default-directory)))
      (when highlight-regexp
        (with-current-buffer buffer
          (setq-local compilation-highlight-regexp highlight-regexp)))
      buffer)))

;;;###autoload
(define-minor-mode ghostel-compile-global-mode
  "Global minor mode: route all `compile'-style calls through ghostel.

When enabled, advises `compilation-start' so that \\[compile],
\\[recompile], \\[project-compile], and every other caller that
goes through `compilation-start' runs in a ghostel terminal —
giving you a real TTY for progress bars, colours, and curses tools
without having to switch commands.

Modes in `ghostel-compile-global-mode-excluded-modes' (by default,
`grep-mode') still use the stock implementation, since their output
parsers and window-management conventions don't fit a live TTY."
  :global t
  :group 'ghostel-compile
  (if ghostel-compile-global-mode
      (advice-add 'compilation-start :around
                  #'ghostel-compile--compilation-start-advice)
    (advice-remove 'compilation-start
                   #'ghostel-compile--compilation-start-advice)))


(provide 'ghostel-compile)

;;; ghostel-compile.el ends here
