lazy val root = (project in file("."))
  .enablePlugins(ScalaJSPlugin)
  .settings(
    name := "UPL",
    scalaVersion := "2.13.14"
  )

// produces the right module.exports for Node.js, but then does not work in browser
// scalaJSLinkerConfig ~= { _.withModuleKind(ModuleKind.CommonJSModule) }

// use @JSExport to mark the objects and methods that should be available from JS
// run "compile" and "fastLinkJS" to build a self-contained main.js holding the dependency closure of the exported methods
// run "package" to create a jar file, or run "assembly" using sbt-assembly plugin -- does not work well because js included

// A plain-JVM Language Server (LSP) for UPL, for editors like Emacs (eglot) that
// speak LSP directly instead of hosting a VS Code extension.
//
// This reuses the *same* core sources as the ScalaJS build (Parser, Checker,
// Project, Interpreter, ...), pulled in unmodified via unmanagedSourceDirectories,
// with only the four VS Code-/browser-specific files excluded (those depend on
// scala.scalajs.js and have no meaning on the JVM). See upl-lsp/README.md.
lazy val uplLsp = (project in file("upl-lsp"))
  .settings(
    name := "upl-lsp",
    scalaVersion := "2.13.14",
    // lsp4j finds RPC methods via reflection over interface default methods
    // (initialized, cancelProgress, ...); Scala's default mixin encoding
    // re-declares those as forwarders in the concrete class, so lsp4j's
    // reflection sees each one twice ("Duplicate RPC method ..."). This flag
    // stops scalac from generating forwarders for methods that already have
    // a default implementation.
    scalacOptions += "-Xmixin-force-forwarders:false",
    Compile / unmanagedSourceDirectories += baseDirectory.value / ".." / "src" / "main" / "scala",
    Compile / unmanagedSources / excludeFilter := {
      // only exclude these from the *shared* directory (the ScalaJS-only bridge
      // files, which don't make sense on the JVM); upl-lsp/src/main/scala has
      // its own local Unicode.scala replacement, which must NOT be excluded
      val sharedDir = (baseDirectory.value / ".." / "src" / "main" / "scala").getCanonicalFile
      val jsOnly = Set("IDE.scala", "WebMain.scala", "FrameIT_Backend.scala", "FrameITProject.scala", "Unicode.scala")
      HiddenFileFilter || new SimpleFileFilter(f =>
        jsOnly(f.getName) && f.getCanonicalPath.startsWith(sharedDir.getPath)
      )
    },
    libraryDependencies += "org.eclipse.lsp4j" % "org.eclipse.lsp4j" % "0.23.1",
    Compile / mainClass := Some("info.kwarc.p.lsp.Main"),
    assembly / mainClass := Some("info.kwarc.p.lsp.Main"),
    assembly / assemblyJarName := "upl-lsp.jar",
    assembly / assemblyMergeStrategy := {
      case PathList("META-INF", xs @ _*) => MergeStrategy.discard
      case _ => MergeStrategy.first
    }
  )
