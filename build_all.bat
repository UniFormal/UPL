call sbt fastLinkJS
cd vscode-extension
call .\makevsix.bat
cd ..
cd jarfile
call .\makejar.bat
cd ..