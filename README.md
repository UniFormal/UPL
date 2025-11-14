This folder contains the implementation and language examples for UPL.

# Implementation

UPL is written in Scala.
src contains the sources of the UPL tool, in particular:
- Syntax: the grammar/AST
- Parser, Checker, Interpreter: the parser, checker, interpreter
- Main, WebMain, IDE: entry points for command line, browser, VSCode extension

# Language examples

'test' contains UPL examples for the UPL language.
Start with 'basics.p', which explains a lot of the basic syntax.
'all.pp' is an example of a UPL project file.

# Build UPL itself

To build, you can use the scripts in
- 'jarfile' to build a self-contained upl.jar file
- 'vscode-extension' to build a upl.vsix file that can be installed as a VSCode extension.

# Write UPL Programs

Install the vsix as a VSCode extension.
Then use the 'test' folder as a workspace for testing and playing with UPL content.

# Develop UPL

It is easiest to open the UPL tool as an IntelliJ project via the scala.sbt file.
The sbt file uses Scala.js to compile to Javascript.
In sbt, use 'compile' to compile (generating *.class file) or 'fastLinkJS' (additinally generating a main.js file).

If you develop UPL, it is easier to skip installing the vsix file (but still generate it) and instead debug it in VSCode 
1. Open the vscode-extension/extension folder (in VSCode)
2. Open the extension.js file
3. Press F5 (alternatively click the rider Run --> Start Debugging)
4. Select Node.js
5. This will spawn a second VSCode window with the extension loaded

