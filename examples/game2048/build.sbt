enablePlugins(ScalaJSPlugin)

name := "Leon-2048"

scalaVersion := "2.11.7"

libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "0.9.0"

unmanagedSourceDirectories in Compile += file("/home/rblanc/vcs/leon/library/")
