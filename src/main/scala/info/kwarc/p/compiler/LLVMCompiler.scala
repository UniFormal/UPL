package info.kwarc.p.compiler

import info.kwarc.p.{File, GlobalContext, Program}

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets
import scala.sys.process.{Process, ProcessLogger}

object LLVMCompiler {
  def run(p: Program, path: File, printDebug: Boolean = true): Unit = {
    val voc = p.voc
    val gc = GlobalContext(voc)

    voc.decls.foreach { d =>
      CoreFragmentChecker(d)(gc, CoreFragmentContext())
    }

    CoreFragmentChecker(p.main)(gc, CoreFragmentContext())

    val llvmIr = compile(p)

    if (printDebug) println(llvmIr)

    // Invokes clang with our llvm IR, redirects the output to stdout and blocks until clang exits.
    val proc = Process(
      Seq(
        "clang",
        "-x",
        "ir",
        "-",
        "-o",
        path.toString
      )
    ).#<(new ByteArrayInputStream(llvmIr.getBytes(StandardCharsets.UTF_8)))
    if (printDebug)
      proc.!
    else
      proc.!(ProcessLogger(_ => (), _ => ()))
  }

  /*
   * Takes all llvm IR and combines it to a valid llvm IR human readable string.
   * */
  def compile(p: Program): String = {
    val ir = IRGenerator.run(p)

    val fnctDecls = ir.declaredFunctions.map(f => f.renderDecl()).mkString("\n")
    val structs = ir.structs.map(s => s.renderStruct()).mkString("\n")
    val globals = ir.globals.map(g => g.renderGlobal()).mkString("\n")
    val fncts = ir.functions.map(f => f.renderFun()).mkString("\n\n")

    s"""
       |$fnctDecls
       |
       |$structs
       |
       |$globals
       |
       |$fncts
       |""".stripMargin
  }
}
