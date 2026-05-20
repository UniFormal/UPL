package info.kwarc.p.compiler

import info.kwarc.p.{File, Program}

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets
import scala.sys.process.Process

object LLVMCompiler {
  def run(p: Program, path: File): Unit = {
    val llvmIr = compile(p)
    println(llvmIr)

    // Invokes clang with our llvm IR, redirects the output to stdout and blocks until clang exits.
    val result = Process(
      Seq(
        "clang",
        "-x",
        "ir",
        "-",
        "-o",
        path.toString
      )
    ).#<(new ByteArrayInputStream(llvmIr.getBytes(StandardCharsets.UTF_8))).!!

    println(result)
  }

  /*
   * Takes all llvm IR and combines it to a valid llvm IR human readable string.
   * */
  def compile(p: Program): String = {
    val ir = IRGenerator.run(p)

    val fnctDecls = ir.declaredFunctions.map(f => f.render()).mkString("\n")
    val strcts = ir.structs.map(s => s.render()).mkString("\n")
    val fncts = ir.functions.map(f => f.render()).mkString("\n")

    s"""
       |$fnctDecls
       |
       |$strcts
       |
       |$fncts
       |""".stripMargin
  }
}
