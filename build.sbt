name := "UPL"
scalaVersion := "2.13.14"
enablePlugins(ScalaJSPlugin)

// produces the right module.exports for Node.js, but then does not work in browser
// scalaJSLinkerConfig ~= { _.withModuleKind(ModuleKind.CommonJSModule) }

// use @JSExport to mark the objects and methods that should be available from JS
// run "compile" and "fastLinkJS" to build a self-contained main.js holding the dependency closure of the exported methods
// run "package" to create a jar file, or run "assembly" using sbt-assembly plugin -- does not work well because js included