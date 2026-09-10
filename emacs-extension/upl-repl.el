;;; upl-repl.el --- Inferior UPL REPL, integrated with `upl-mode' -*- lexical-binding: t; -*-

;; Author: (your postdoc's UPL project)
;; Keywords: languages, processes
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1"))

;;; Commentary:

;; A comint-based inferior UPL REPL, plus commands to send code from a
;; `upl-mode' buffer into it -- the same idea as `inferior-lisp'/`cider'/
;; `run-python', but for UPL.
;;
;; This wraps the compiler's own `--repl' mode (`info.kwarc.p.Main', see
;; `Project.repl' in Project.scala): a plain line-based prompt REPL that
;; reads one expression per line from stdin and prints its type and value.
;; It ships in the same jar as the language server
;; (upl-lsp/target/scala-2.13/upl-lsp.jar has both `info.kwarc.p.Main' and
;; `info.kwarc.p.lsp.Main' as classes), so if you've already built that for
;; eglot, there's nothing new to build for this.
;;
;; The REPL only accepts *expressions* (which in UPL includes `val'/`var'
;; bindings, per the language's design -- see basics.p) -- not top-level
;; `module'/`type'/function declarations. Point it at your project's
;; sources on startup and it type-checks and loads them all, and you use
;; the REPL to evaluate/test against what's already declared there, define
;; scratch bindings, etc.
;;
;; Installation:
;;
;;   (require 'upl-mode)   ; optional but recommended, for the keybindings
;;   (require 'upl-repl)
;;   (setq upl-repl-jar "/path/to/upl-lsp.jar")
;;
;; Usage: `M-x upl-repl' (or `C-c C-r' in a upl-mode buffer) to start/switch
;; to the REPL, prompting for which file/folder/project to load. From a
;; upl-mode buffer: `C-c C-c' sends the region (or current line) to the
;; REPL; `C-c C-l' flattens a multi-line region into one REPL input line;
;; `C-c C-b' sends the whole buffer.

;;; Code:

(require 'comint)

;; defined in upl-mode.el; declared here only to satisfy the byte-compiler
;; when upl-repl.el is compiled standalone
(defvar upl-mode-map)

(defgroup upl-repl nil
  "Inferior UPL REPL."
  :prefix "upl-repl-"
  :group 'languages)

(defcustom upl-repl-jar nil
  "Path to a jar with `info.kwarc.p.Main' on its classpath.
The upl-lsp fat jar (upl-lsp/target/scala-2.13/upl-lsp.jar) has this
class alongside the language server, so the same jar built for eglot
works here unchanged."
  :type '(choice (const :tag "Not set" nil) file)
  :group 'upl-repl)

(defcustom upl-repl-java-program "java"
  "Java executable used to launch the UPL REPL."
  :type 'string
  :group 'upl-repl)

(defcustom upl-repl-buffer-name "*upl-repl*"
  "Name of the buffer used for the UPL REPL process."
  :type 'string
  :group 'upl-repl)

(defun upl-repl--jar ()
  (or upl-repl-jar
      (user-error "`upl-repl-jar' is not set; e.g. (setq upl-repl-jar \"/path/to/upl-lsp.jar\")")))

(defun upl-repl--default-path ()
  "A reasonable default path to feed the REPL: the current file if
we're visiting a UPL source, else the current directory."
  (or (and buffer-file-name (derived-mode-p 'upl-mode) buffer-file-name)
      default-directory))

;;;###autoload
(defun upl-repl (path)
  "Start (or switch to) the UPL REPL, which loads and type-checks PATH
\(a .p/.upl source file, a .pp project file, or a folder of sources)
on startup, exactly like running `java -cp JAR info.kwarc.p.Main
--repl PATH' by hand."
  (interactive
   (list (let ((default (upl-repl--default-path)))
           (read-file-name "UPL project/source path: "
                            (file-name-directory default) default t
                            (file-name-nondirectory default)))))
  (let ((buf (get-buffer-create upl-repl-buffer-name))
        (jar (upl-repl--jar))
        (full-path (expand-file-name path)))
    (unless (comint-check-proc buf)
      (with-current-buffer buf
        (apply #'make-comint-in-buffer "upl-repl" buf
               upl-repl-java-program nil
               (list "-cp" jar "info.kwarc.p.Main" "--repl" full-path))
        (upl-repl-mode)))
    (pop-to-buffer buf)))

(defvar upl-repl-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `upl-repl-mode'.")

(define-derived-mode upl-repl-mode comint-mode "UPL-REPL"
  "Major mode for an inferior UPL REPL process."
  (setq-local comint-prompt-regexp "^> ")
  (setq-local comint-prompt-read-only t))

;;; sending code from a upl-mode (or any) buffer into the REPL

(defun upl-repl--buffer ()
  (or (get-buffer upl-repl-buffer-name)
      (user-error "No UPL REPL running; start one with `M-x upl-repl'")))

(defun upl-repl--send-line (line)
  "Send one already-flattened LINE of source to the REPL as a single input."
  (let* ((buf (upl-repl--buffer))
         (proc (get-buffer-process buf)))
    (unless proc (user-error "UPL REPL process is not running"))
    (comint-send-string proc (concat (string-trim line) "\n"))
    (display-buffer buf)))

(defun upl-repl-send-line ()
  "Send the current line to the UPL REPL as one expression."
  (interactive)
  (upl-repl--send-line (thing-at-point 'line t)))

(defun upl-repl-send-region (start end)
  "Send each source line in the region to the UPL REPL as a separate
input. Use this for a block of standalone one-line expressions (e.g.
a few ASSERTs written one per line). For a single expression that
happens to span multiple lines, use
`upl-repl-send-region-flattened' instead: the REPL reads one
expression per input line, so sent naively, a multi-line expression
would arrive as several separate (and likely incomplete) ones."
  (interactive "r")
  (dolist (line (split-string (buffer-substring-no-properties start end) "\n" t "[ \t]+"))
    (upl-repl--send-line line)))

(defun upl-repl-send-region-flattened (start end)
  "Send the region to the UPL REPL as a single input line, joining its
source lines with spaces first. Use this for one expression spanning
multiple lines -- safe because UPL is not whitespace-sensitive (see
upl-mode's indentation notes)."
  (interactive "r")
  (upl-repl--send-line
   (replace-regexp-in-string "[ \t]*\n[ \t]*" " "
                              (buffer-substring-no-properties start end))))

(defun upl-repl-send-dwim ()
  "Send the active region (one REPL input per source line), or the
current line if no region is active."
  (interactive)
  (if (use-region-p)
      (upl-repl-send-region (region-beginning) (region-end))
    (upl-repl-send-line)))

(defun upl-repl-send-buffer ()
  "Send the whole current buffer to the UPL REPL, one input per source line."
  (interactive)
  (upl-repl-send-region (point-min) (point-max)))

(defun upl-repl-quit ()
  "Tell the UPL REPL to exit."
  (interactive)
  (upl-repl--send-line "exit"))

;; convenience bindings in upl-mode buffers, mirroring SLIME/CIDER/ESS conventions
(with-eval-after-load 'upl-mode
  (define-key upl-mode-map (kbd "C-c C-r") #'upl-repl)
  (define-key upl-mode-map (kbd "C-c C-c") #'upl-repl-send-dwim)
  (define-key upl-mode-map (kbd "C-c C-l") #'upl-repl-send-region-flattened)
  (define-key upl-mode-map (kbd "C-c C-b") #'upl-repl-send-buffer)
  (define-key upl-mode-map (kbd "C-c C-q") #'upl-repl-quit))

(provide 'upl-repl)

;;; upl-repl.el ends here
