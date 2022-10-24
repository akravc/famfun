lazy val root = (project in file("."))
  .settings(
    name := "famfun",
    scalaVersion := "3.2.0",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
    libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.14",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.14"
  )

Compile / scalaSource := baseDirectory.value / "src"

Test / scalaSource := baseDirectory.value / "test"
