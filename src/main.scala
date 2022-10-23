import famfun.*
import TestFamParser.*
import PrettyPrint.*
import name_resolution.*
import type_checking.*
import code_generation.*

import java.io.File
import java.io.PrintWriter
import scala.io.Source

object famfun_main {
  def typecheckProcess(inp: String): Either[String, Unit] = {
    val parsed = parse0(pProgram, inp)
    parsed match {
      case Success(result, _) =>
        resolveVarsAndValidateSelfPaths(result).flatMap { progLkg =>
          init(progLkg)
          typeCheckLinkage(progLkg)
        }
    }
  }

  def main(args: Array[String]): Unit = {
    val sourceFilename = if (args.length>0) args(0) else "res/pretty_example"
    val buf = Source.fromFile(sourceFilename)
    val inp = buf.getLines.mkString("\n")
    buf.close()
    val parsed = parse0(pProgram, inp)
    parsed match {
      case Success(result, _) =>
        //println(result)
        resolveVarsAndValidateSelfPaths(result).flatMap { progLkg =>
          init(progLkg)
          typeCheckLinkage(progLkg)
        } match {
          case Left(msg) => println(msg)
          case Right(_) =>
            println("Type-checking succeeded")
            generateCode(cache.values).foreach { (fileName, contents) =>
              val file = new File(s"test/gen/$fileName")
              file.createNewFile()
              val writer = new PrintWriter(file)
              writer.write(contents)
              writer.close()
            }
        }
      case _ => println(parsed)
    }
  }
}
