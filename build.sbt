// UPL itself
lazy val root = (project in file("."))
  .enablePlugins(ScalaJSPlugin)
  .settings(
    name := "UPL",
    scalaVersion := "2.13.14",
  )

// FrameIT Scrollview: Browser UI on top of UPL's FrameIT backend (Laminar/Airstream); Seperate project, so that UPL's own main.js stays free of DOM code (also runs in Node.js)
// Build: sbt frameitScrollView/fastLinkJS, Output: frameit-scrollview/target/scala-2.13/frameit-scrollview-fastopt/main.js
lazy val frameitScrollView = (project in file("frameit-scrollview"))
  .enablePlugins(ScalaJSPlugin) // Compile Scala to JavaScript
  .dependsOn(root) // UPL's classes can be used directly; UPL does not know the ScrollView
  .settings(
    name := "frameit-scrollview",
    // Laminar 17.2.0 pulls in scala-library 2.13.15; the compiler must not be older
    scalaVersion := "2.13.15",
    libraryDependencies ++= Seq(
      "org.scala-js" %%% "scalajs-dom" % "2.8.0", // Typed access to the browser DOM, %%% selects the Scala.js build of a library
      "com.raquo" %%% "laminar" % "17.2.0", // UI library, includes Airstream (reactive values)
    ),
    scalaJSUseMainModuleInitializer := true, // Run main() when main.js is loaded
    Compile / mainClass := Some("info.kwarc.p.frameit.ScrollViewMain"), // Entry point of the ScrollView
  )
