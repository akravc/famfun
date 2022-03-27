lazy val root = (project in file("."))
  .settings(
    name := "famfun",
    scalaVersion := "3.0.0",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.0.0",
    libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.9",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9"
  )

Compile / scalaSource := baseDirectory.value / "src"

Test / scalaSource := baseDirectory.value / "test"
