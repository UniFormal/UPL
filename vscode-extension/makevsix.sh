!#/bin/sh
copy /Y ..\target\scala-2.13\upl-fastopt\* extension\src
echo module.exports = {VSCodeBridge}; >> extension\src\main.js
zip -r upl-vscode.vsix * -x makevsix.bat