lazy val root = (project in file("."))
  .settings(
    name := "famlang",
    scalaVersion := "3.0.0",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.0.0",
    libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.9",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test"
  )
