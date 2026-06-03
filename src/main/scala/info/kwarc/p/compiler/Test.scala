package info.kwarc.p.compiler

import info.kwarc.p.{
  Checker,
  ErrorThrower,
  File,
  GlobalContext,
  Interpreter,
  PError,
  Program,
  Project,
  UnitValue
}

import scala.sys.process.Process

/** A simple test framework to check that the compiler and interpreter produce the same output.
  * It currently checks the toString result of the Interpreter against the output code from executing the binary
  * produced by the compiler.
  *
  * This limits the scope of testing (because we are limited to the valid exit integers 0-255).
  * In the future it may be wise to extend this, once we implement printing in the compiler.
  */
object Test {
  val TEST_DIR = File("test/compiler/test")
  val TMP_FILE = File("tmp.out")

  def main(args: Array[String]): Unit = {
    TEST_DIR.descendants
      .filter(p => p.getExtension.contains("pp"))
      .foreach { p =>
        val proj = Project.fromFile(p, None)

        val voc = proj.check(false)

        if (proj.checkErrors()) {
          return
        }
        val mn = proj.main.getOrElse(UnitValue)
        val ch = new Checker(ErrorThrower)
        try {
          val (eC, _) = ch.checkAndInferExpression(GlobalContext(voc), mn)
          val prog = Program(voc, eC)

          try {
            val compilerResult = compileAndRun(prog)
            val interpreterResult = interpret(prog)

            if (compilerResult != interpreterResult) {
              System.err.println(
                s"$p failed (compiler and interpreter output differ):"
              )
              System.err.println(s"Compiler output: $compilerResult")
              System.err.println(s"Interpreter output: $interpreterResult")
            } else {
              println(s"$p passed successfully.")
            }
          } catch {
            case e: Throwable =>
              System.err.println(s"$p failed to compare: $e")
          }

        } catch {
          case e: PError =>
            println(s"Failed to check $p: $e")
        }
      }
    TMP_FILE.toJava.delete()
  }

  def compileAndRun(prog: Program): String = {
    LLVMCompiler.run(prog, TMP_FILE, printDebug = false)
    Process(
      Seq(
        s"./${TMP_FILE.toString}"
      )
    ).!.toString
  }

  def interpret(prog: Program): String = {
    val (_, r) = Interpreter.run(prog)
    r.toString
  }
}
