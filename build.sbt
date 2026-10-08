lazy val root = (project in file("."))
  .enablePlugins(ScalaJSPlugin)
  .settings(
    name := "UPL",
    scalaVersion := "2.13.14",
  )


lazy val frameitScrollView = (project in file("frameit-scrollview"))
  .enablePlugins(ScalaJSPlugin)
  .dependsOn(root)
  .settings(
    name := "frameit-scrollview",
    scalaVersion := "2.13.15",
    libraryDependencies ++= Seq(
      "org.scala-js" %%% "scalajs-dom" % "2.8.0",
      "com.raquo" %%% "laminar" % "17.2.0",
    ),
    scalaJSUseMainModuleInitializer := true,
    Compile / mainClass := Some("info.kwarc.p.frameit.ScrollViewMain"),
  )
