# upl-mode

An Emacs major mode for UPL (`info.kwarc.p`), derived from the project's
own TextMate grammar (`vscode-extension/extension/syntaxes/upl.tmGrammar.json`)
and the keyword tables in `src/main/scala/info/kwarc/p/Parser.scala` and
`Notation.scala`.

## Features

- Syntax highlighting: control keywords (`if`/`while`/`match`/`catch`/...),
  declaration keywords (`module`/`theory`/`val`/`var`/`type`/`include`/`realize`/...),
  built-in types (`int`/`rat`/`float`/`set`/`list`/...), constants
  (`true`/`false`/`univ`), built-ins (`ASSERT`/`CAST`), fixity declarations
  (`infix`, `_prefix_`, etc.), module/theory/type names, annotations (`@foo`),
  and top-level declaration names.
- `//` line comments and `/* ... */` block comments (`M-;` works as usual).
- Bracket-depth-based indentation (`{}`/`()`/`[]`) — validated against the
  project's own example files: stripping all indentation from
  `test/examples/*.p` and letting `upl-mode` reindent from scratch reproduces
  the original files exactly.
- `imenu` support for modules/theories, `type` declarations, and top-level
  value/function declarations.
- Auto-enabled for `.p`, `.upl`, `.p.tex`, and `.pp` files.

## Installation

Copy `upl-mode.el` somewhere on your `load-path`, e.g. `~/.emacs.d/lisp/`,
then add to your init file:

```elisp
(add-to-list 'load-path "~/.emacs.d/lisp/")
(require 'upl-mode)
```

Or with `use-package`:

```elisp
(use-package upl-mode
  :load-path "/home/royaleinstein/Documents/UPL/emacs-extension")
```

Or with `straight.el`/`quelpa` pointing at a local recipe, if you prefer to
keep this directory in place instead of copying the file.

No external dependencies; works on stock Emacs 26.1+.

## LSP (eglot)

See `../upl-lsp/README.md` for a standalone JVM language server (real
diagnostics/hover/completion/definition/outline, backed by the actual
checker) and the `eglot-server-programs` config to point at it.

## REPL

`upl-repl.el` gives you an inferior UPL REPL (comint-based, like
`inferior-lisp`/`cider`), wrapping the compiler's own `--repl` mode. It
reuses the same jar built for eglot (`upl-lsp.jar` has both the language
server and the CLI/REPL entry point).

```elisp
(require 'upl-repl)
(setq upl-repl-jar "/home/royaleinstein/Documents/UPL/upl-lsp/target/scala-2.13/upl-lsp.jar")
```

In a `upl-mode` buffer:

| Key       | Command                          | Does                                                            |
|-----------|-----------------------------------|------------------------------------------------------------------|
| `C-c C-r` | `upl-repl`                        | start/switch to the REPL, prompting for what to load             |
| `C-c C-c` | `upl-repl-send-dwim`              | send region (one REPL input per line) or current line            |
| `C-c C-l` | `upl-repl-send-region-flattened`  | join a multi-line region into one input (for one multi-line expr)|
| `C-c C-b` | `upl-repl-send-buffer`            | send the whole buffer, one input per line                        |
| `C-c C-q` | `upl-repl-quit`                   | send `exit`                                                       |

The REPL only accepts *expressions* per input line (that includes `val`/`var`
bindings — see `basics.p` on why), not `module`/`type`/toplevel-function
declarations, and it reads one input per line — so a single expression that
spans multiple lines needs `upl-repl-send-region-flattened` (safe because
UPL isn't whitespace-sensitive), while several one-line statements should go
through the line-by-line `upl-repl-send-region`/`-dwim`/`-buffer` instead.
Mixing the two (flattening multiple statements together) can silently fuse
them via UPL's `f x` juxtaposition-application syntax — tested and confirmed
this actually happens, it doesn't just look risky on paper.

Point the REPL (`M-x upl-repl`) at a file, folder, or `.pp` project file —
it type-checks everything there first, then you can evaluate/test against
whatever it declared.

## Notes for keeping this in sync with the language


- `src/main/scala/info/kwarc/p/Parser.scala` — search for `startsWithS`/
  `startsWithAny` calls and the `Keywords` object for reserved words.
- `src/main/scala/info/kwarc/p/Notation.scala` — the fixity keyword list
  (`prefix`, `infix-left`, etc.).

Update the `upl-*-keywords` constants near the top of `upl-mode.el`
accordingly.
