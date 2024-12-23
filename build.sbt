name := "UPL"
scalaVersion := "2.13.14"
enablePlugins(ScalaJSPlugin)

// use @JSExport to mark the objects and methods that should be available from JS
// run "compile" and "fastLinkJS" to build a self-contained main.js holding the dependency closure of the exported methods
// run "package" to create a jar file