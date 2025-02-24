:: as compiled by sbt fastLinkJS
copy /Y ..\target\scala-2.13\upl-fastopt\* extension\src
:: workaround: Scala.js apparently cannot generate a js file that both Node and browsers like
:: here: add the export declaration that Node wants to have
echo module.exports = {VSCodeBridge}; >> extension\src\main.js
:: build the VSCode extension package (excluding this script)
zip -r upl-vscode.vsix * -x makevsix.bat makevsix.sh