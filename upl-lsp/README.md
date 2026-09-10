# upl-lsp

A standalone Language Server Protocol (LSP) implementation for UPL, running
as a plain JVM process. No Node.js, no VS Code — any LSP-capable editor
(Emacs/eglot, lsp-mode, Neovim, coc.nvim, Helix, ...) can talk to it directly
over stdio.

## Why this works / how it's structured

The VS Code extension (`vscode-extension/`) does *not* use LSP at all — it
calls straight into a ScalaJS-compiled bridge class (`VSCodeBridge` in
`src/main/scala/info/kwarc/p/IDE.scala`) from inside the VS Code process.
That bridge is a thin wrapper around `info.kwarc.p.Project`/`Checker`, which
have no dependency on ScalaJS or VS Code at all — of the ~11k lines in
`src/main/scala/info/kwarc/p`, only 4 files (`IDE.scala`, `WebMain.scala`,
`FrameIT_Backend.scala`, `FrameITProject.scala`) touch `scala.scalajs.js`,
and none of the core parser/checker/interpreter files depend on them.

So this project is a second, LSP-native bridge with the same shape as
`VSCodeBridge`, compiled for the JVM instead of JS:

- `build.sbt` defines a second subproject, `uplLsp` (root dir `upl-lsp/`),
  which pulls in the shared sources from `../src/main/scala` unmodified via
  `unmanagedSourceDirectories`, excluding only the 4 JS-only files above.
- `Unicode.scala` needs one JVM-local copy (`upl-lsp/src/main/scala/info/kwarc/p/Unicode.scala`)
  because the original has one unused `scala.scalajs.js` import; everything
  else in it is plain `java.lang.Character` logic and is copied verbatim.
- `info.kwarc.p.lsp.*` (this package) is the actual LSP server: it uses
  [Eclipse LSP4J](https://github.com/eclipse-lsp4j/lsp4j) for JSON-RPC/stdio
  framing and LSP data types, and otherwise calls the exact same `Project`
  methods `VSCodeBridge` calls (`updateAndCheck`, `fragmentAt`, `lookupRef`,
  `getVocabulary`, ...). Diagnostics, hover, go-to-definition, completion,
  signature help, and document outline are all backed by the real
  parser/checker — nothing is reimplemented.

The ScalaJS build (`sbt compile`, `sbt fastLinkJS`, the VS Code extension)
is untouched by any of this; `uplLsp` is a wholly separate, additive
subproject.

## Building

```sh
sbt uplLsp/assembly
```

produces `upl-lsp/target/scala-2.13/upl-lsp.jar`, a self-contained runnable
jar (LSP4J and its few dependencies included).

## Running standalone (for testing)

```sh
java -jar upl-lsp/target/scala-2.13/upl-lsp.jar
```

talks LSP (`Content-Length`-framed JSON-RPC) over stdin/stdout. There's
nothing to see when you run it directly — it just waits for a client.

## Using with Emacs (eglot)

```elisp
(require 'upl-mode)   ; see ../emacs-extension
(require 'eglot)

(add-to-list 'eglot-server-programs
             '(upl-mode . ("java" "-jar" "/home/royaleinstein/Documents/UPL/upl-lsp/target/scala-2.13/upl-lsp.jar")))
```

Then open a `.p` file and run `M-x eglot`. You should get:

- live diagnostics from the real type checker as you edit
- `eglot-hover-eldoc-function` / `K` (via `eldoc`): hover info for
  references, variables, operators, and types
- `M-.` (`xref-find-definitions`): go to definition
- completion-at-point / company/corfu integration
- `imenu`/`consult-imenu`: document outline (also works standalone via
  `upl-mode`'s own `imenu-generic-expression`, but eglot's version is
  checker-backed so it reflects the current parse)

## Current limitations (all fixable, not fundamental)

- **Diagnostics are per-file only.** Like `VSCodeBridge`, cross-file
  declarations are resolved via `Project`, but a file is only (re)checked
  when *it* changes — editing a file that others `include` doesn't
  currently re-publish their diagnostics. `VSCodeBridge` has the same
  property.
- **Go-to-definition across files** resolves a `Location`'s `SourceOrigin`
  back to a URI by assuming `origin.container` is already a URI (true for
  documents opened via `didOpen`, since we key `Project` entries by URI
  directly). It won't find declarations in files that were never opened
  in the editor. A `didOpen`/preload pass over the project's sources, or
  resolving via `initialize`'s `rootUri`, would fix this.
- **No incremental sync** — the server advertises
  `TextDocumentSyncKind.Full`, so every keystroke round-trips the whole
  document text. Fine for the source sizes in `test/`; would want
  incremental sync for large files.
- **No workspace-wide features** (workspace symbol search, rename,
  find-references) — `UplWorkspaceService` is a stub. `Project` doesn't
  currently track a reverse reference index, so these would need that
  first.
- Position encoding assumes UTF-16 code units (the LSP default); fine for
  ASCII/Latin identifiers, and UPL source is mostly that, but multi-byte
  Unicode identifiers spanning a surrogate pair could throw off column
  numbers by one. Not exercised by the current test corpus.

## Keeping in sync with the language

Same note as `../emacs-extension/README.md`: if new syntax/behavior is added
to the checker, this server picks it up for free (it calls the same
`Project`/`Checker` code VS Code uses) — nothing here needs updating unless
the *shape* of diagnostics/declarations/references changes.
