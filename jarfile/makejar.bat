cd ..\target\scala-2.13\classes
zip -r ..\..\..\jarfile\upl.jar . -i *.class
cd ..\..\..\jarfile
zip upl.jar META-INF\MANIFEST.MF
