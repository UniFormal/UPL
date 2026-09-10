;;; upl-mode.el --- Major mode for editing UPL source files -*- lexical-binding: t; -*-

;; Author: (your postdoc's UPL project)
;; Keywords: languages
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1"))

;;; Commentary:

;; A major mode for UPL (info.kwarc.p), the language whose compiler
;; lives in src/main/scala/info/kwarc/p.  This mode was derived from
;; the project's own TextMate grammar
;; (vscode-extension/extension/syntaxes/upl.tmGrammar.json) and from
;; the keyword tables in Parser.scala/Notation.scala, so it should stay
;; easy to keep in sync as the language evolves.
;;
;; Features:
;;  - syntax highlighting (keywords, types, builtins, fixity
;;    declarations, module/theory/type/function names, annotations)
;;  - `//' line comments and `/* ... */' block comments
;;  - paren/bracket/brace-depth based indentation
;;  - imenu support for modules/theories, type declarations, and
;;    top-level function/value declarations
;;
;; Installation: put this file on your `load-path' and
;;
;;   (require 'upl-mode)
;;
;; or, with use-package,
;;
;;   (use-package upl-mode :load-path "/path/to/emacs-extension")
;;
;; Files with extension .p, .upl, .p.tex, and .pp are associated with
;; `upl-mode' automatically.

;;; Code:

(defgroup upl nil
  "Major mode for editing UPL source files."
  :prefix "upl-"
  :group 'languages)

(defcustom upl-indent-offset 2
  "Number of columns to indent per nesting level in `upl-mode'.
The example sources in the UPL repository consistently use 2
spaces per level, so that is the default here."
  :type 'integer
  :safe #'integerp
  :group 'upl)

;;; Syntax table

(defvar upl-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; identifiers may contain underscores (fixity markers like
    ;; _prefix_ and _infix_ rely on this)
    (modify-syntax-entry ?_ "_" table)
    ;; strings, with backslash escapes
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?\\ "\\" table)
    ;; // line comments and /* ... */ block comments, C++-style
    (modify-syntax-entry ?/ ". 124" table)
    (modify-syntax-entry ?* ". 23b" table)
    (modify-syntax-entry ?\n ">" table)
    ;; operator characters are plain punctuation, not symbol
    ;; constituents, so words like "x->y" still separate x from y
    (dolist (ch '(?+ ?- ?= ?< ?> ?& ?| ?! ?% ?^ ?~ ?@ ?# ?\; ?: ?, ?? ?$))
      (modify-syntax-entry ch "." table))
    table)
  "Syntax table used in `upl-mode'.")

;;; Keyword tables
;; Mirrors vscode-extension/extension/syntaxes/upl.tmGrammar.json and
;; the `Keywords'/`CollectionKind' tables in Parser.scala/Syntax.scala.

(defconst upl-control-keywords
  '("if" "else" "while" "for" "in" "match" "catch"
    "return" "throw" "exists" "forall" "Forall")
  "Control-flow and binder keywords.")

(defconst upl-declaration-keywords
  '("module" "theory" "include" "realize"
    "open" "closed" "mutable" "var" "val" "type")
  "Keywords that introduce or modify declarations.")

(defconst upl-type-keywords
  '("int" "nat" "rat" "comp" "float" "bool" "string"
    "set" "list" "bag" "option" "any" "exn" "empty")
  "Names of built-in types and collection kinds.")

(defconst upl-constant-keywords
  '("true" "false" "univ")
  "Built-in constants.")

(defconst upl-builtin-keywords
  '("ASSERT" "CAST")
  "Built-in pseudo-functions handled specially by the parser.")

(defconst upl-fixity-keywords
  '("prefix" "postfix"
    "infix" "infix-assoc" "infix-left" "infix-right"
    "circumfix" "circumfix-flex"
    "applyfix" "applyfix-flex"
    "bindfix" "bindfix-assoc")
  "Keywords used to declare the fixity/notation of an operator.")

(defconst upl-font-lock-keywords
  (list
   ;; module/theory NAME { ... }
   '("\\<\\(module\\|theory\\)\\>[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)"
     (1 font-lock-keyword-face) (2 font-lock-type-face))
   ;; include/realize NAME
   '("\\<\\(include\\|realize\\)\\>[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)"
     (1 font-lock-keyword-face) (2 font-lock-type-face))
   ;; type NAME = ...
   '("\\<type\\>[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)"
     (1 font-lock-type-face))
   ;; _prefix_+, _infix_==, etc.
   '("\\(_prefix_\\|_infix_\\|_circumfix_\\|_postfix_\\|_applyfix_\\|_bindfix_\\)\\(\\S-+\\)"
     (1 font-lock-keyword-face) (2 font-lock-function-name-face))
   ;; prefix +, infix-left ==, etc.
   (cons (concat "\\<\\(" (regexp-opt upl-fixity-keywords) "\\)\\>[ \t]+\\(\\S-+\\)")
         '((1 font-lock-keyword-face) (2 font-lock-function-name-face)))
   ;; annotations: @name
   '("\\(@\\)\\([a-zA-Z_][a-zA-Z0-9_]*\\)"
     (1 font-lock-preprocessor-face) (2 font-lock-variable-name-face))
   ;; control keywords
   (cons (concat "\\<\\(" (regexp-opt upl-control-keywords) "\\)\\>") 'font-lock-keyword-face)
   ;; declaration keywords
   (cons (concat "\\<\\(" (regexp-opt upl-declaration-keywords) "\\)\\>") 'font-lock-keyword-face)
   ;; built-in types
   (cons (concat "\\<\\(" (regexp-opt upl-type-keywords) "\\)\\>") 'font-lock-type-face)
   ;; built-in constants
   (cons (concat "\\<\\(" (regexp-opt upl-constant-keywords) "\\)\\>") 'font-lock-constant-face)
   ;; built-in pseudo-functions
   (cons (concat "\\<\\(" (regexp-opt upl-builtin-keywords) "\\)\\>") 'font-lock-builtin-face)
   ;; numbers
   '("\\<[0-9]+\\(\\.[0-9]+\\)?\\>" . font-lock-constant-face)
   ;; top-level declaration names: `name(...)? : ...' or `name(...)? = ...'
   '("^[ \t]*\\([a-zA-Z_][a-zA-Z0-9_]*\\)[ \t]*\\((.*?)\\)?[ \t]*[:=]"
     (1 font-lock-function-name-face))
   ;; the wildcard/anonymous-name placeholder
   '("\\<_\\>" . font-lock-variable-name-face))
  "Font-lock keyword table for `upl-mode'.")

;;; Indentation
;; UPL is not whitespace-sensitive; blocks are delimited by
;; {}/()/[] as in most C-family languages, so a simple
;; nesting-depth indentation (as reported by `syntax-ppss') matches
;; the style used throughout the example sources.

(defun upl--leading-close-count ()
  "Count the closing bracket characters at the start of the current line."
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t")
    (let ((n 0))
      (while (and (not (eolp)) (eq (char-syntax (char-after)) ?\)))
        (setq n (1+ n))
        (forward-char 1)
        (skip-chars-forward " \t"))
      n)))

(defun upl--indentation-depth ()
  "Return the desired indentation depth (in levels) for the current line."
  (save-excursion
    (beginning-of-line)
    (let ((depth (car (syntax-ppss (point))))
          (closers (upl--leading-close-count)))
      (max 0 (- depth closers)))))

(defun upl-indent-line ()
  "Indent the current line in `upl-mode'."
  (interactive)
  (let* ((savep (> (current-column) (current-indentation)))
         (indent (* upl-indent-offset (upl--indentation-depth))))
    (if savep
        (save-excursion (indent-line-to indent))
      (indent-line-to indent))
    (when (< (current-column) indent)
      (move-to-column indent))))

;;; Imenu

(defvar upl-imenu-generic-expression
  '(("Module/Theory" "^[ \t]*\\(?:module\\|theory\\)[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1)
    ("Type" "^[ \t]*type[ \t]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1)
    ("Declaration" "^[ \t]*\\([a-zA-Z_][a-zA-Z0-9_]*\\)[ \t]*(?.*?)?[ \t]*[:=]" 1))
  "Value for `imenu-generic-expression' in `upl-mode'.")

;;; Major mode definition

;;;###autoload
(define-derived-mode upl-mode prog-mode "UPL"
  "Major mode for editing UPL source files.

\\{upl-mode-map}"
  :syntax-table upl-mode-syntax-table
  (setq-local font-lock-defaults '(upl-font-lock-keywords nil nil nil nil))
  (setq-local comment-start "// ")
  (setq-local comment-end "")
  (setq-local comment-start-skip "\\(//+\\|/\\*+\\)[ \t]*")
  (setq-local indent-line-function #'upl-indent-line)
  (setq-local indent-tabs-mode nil)
  (setq-local imenu-generic-expression upl-imenu-generic-expression)
  (setq-local electric-indent-chars
              (append '(?\} ?\) ?\]) electric-indent-chars)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.upl\\'" . upl-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.p\\.tex\\'" . upl-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pp\\'" . upl-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.p\\'" . upl-mode))

(provide 'upl-mode)

;;; upl-mode.el ends here
