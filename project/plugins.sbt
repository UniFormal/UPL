addSbtPlugin("org.scala-js" % "sbt-scalajs" % "1.17.0")
// used only by the plain-JVM `upl-lsp` subproject (see build.sbt) to build a
// runnable fat jar for the language server; irrelevant to the ScalaJS build.
addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "2.3.0")