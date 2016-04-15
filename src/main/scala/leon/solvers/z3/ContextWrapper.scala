/* Copyright 2009-2016 EPFL, Lausanne */

package leon.solvers.z3

import java.util.zip.ZipInputStream

import com.microsoft.z3.Context

import java.io.{FileOutputStream, File}
import java.security.CodeSource
import scala.collection.JavaConversions._

object ContextWrapper {
  private val DS = java.io.File.separator
  private val PS = java.io.File.pathSeparator
  private val LIB_BIN     = DS + "lib-bin" + DS
  private val LIB_NAME    = "z3java"
  private val LIBZ3_NAME  = "z3"

  private def extractFromJar(toDir: File) {
    val src: CodeSource = classOf[Context].getProtectionDomain.getCodeSource
    if (src != null) {
      val jar = src.getLocation
      val zip = new ZipInputStream(jar.openStream())
      while(true) {
        val e = zip.getNextEntry
        if (e == null) return

        val path = e.getName

        if (path.startsWith("lib-bin/") && !e.isDirectory) {

          val name = new File(path).getName

          val to = new File(toDir.getAbsolutePath + DS + name)

          val in = classOf[Context].getResourceAsStream("/"+path)
          val out = new FileOutputStream(to)
          val buf = new Array[Byte](4096)

          var len: Int = in.read(buf)
          while (len > 0) {
            out.write(buf, 0, len)
            len = in.read(buf)
          }

          out.close()
          in.close()
        }
      }
    }

  }

  private def addLibraryPath(pathToAdd: String): Unit = {
    println(System.getProperty("java.library.path"))
    System.setProperty("java.library.path", pathToAdd + PS + System.getProperty("java.library.path"))
    println(System.getProperty("java.library.path"))

    // this forces JVM to reload "java.library.path" property
    val fieldSysPath = classOf[ClassLoader].getDeclaredField("sys_paths")
    fieldSysPath.setAccessible(true)
    fieldSysPath.set(null, null)
  }

  private def loadFromJar() {
    val path = "SCALAZ3_BIN"
    val libDir = new File(System.getProperty("java.io.tmpdir") + DS + path + LIB_BIN)

    //System.mapLibraryName(LIB_NAME)
    //System.mapLibraryName(LIBZ3_NAME)

    try {
      if (!libDir.isDirectory || !libDir.canRead) {
        libDir.mkdirs()
        extractFromJar(libDir)
      }
      addLibraryPath(libDir.getAbsolutePath)
      //System.loadLibrary(LIBZ3_NAME)
      System.loadLibrary(LIB_NAME)
    } catch {
      case e: Throwable =>
        e.printStackTrace()
    }
  }

  private var extracted = false

  def mkContext(z3Cfg: Map[String, String]): Context = {
    if (!extracted) synchronized { loadFromJar() }
    try {
      new Context(z3Cfg)
    } catch {
      case e: Exception =>
        e.printStackTrace()
        throw e
    } finally {
      extracted = true
    }

  }
}
