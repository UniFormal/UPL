package info.kwarc.p.compiler

import info.kwarc.p._

import java.io.{ByteArrayOutputStream, PrintStream}
import scala.sys.process.{Process, ProcessLogger}

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
        val mn = proj.main.getOrElse(Unit.Value)
        val ch = new Checker(ErrorThrower)
        try {
          val (eC, _) = ch.checkAndInferExpression(GlobalContext(voc), mn)
          val prog = Program(voc, eC)

          try {
            val (compilerResult, compilerStdout) = compileAndRun(prog)
            val (interpreterResult, interpreterStdout) = interpret(prog)

            if (compilerResult != interpreterResult) {
              System.err.println(s"$p failed (compiler and interpreter result differ):")
              System.err.println(s"Compiler result: $compilerResult")
              System.err.println(s"Interpreter result: $interpreterResult")
            } else if (compilerStdout != interpreterStdout) {
              System.err.println(s"$p failed (compiler and interpreter output differ):")
              System.err.println(s"Compiler output: \"$compilerStdout\"")
              System.err.println(s"Interpreter output: \"$interpreterStdout\"")
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
  }

  def compileAndRun(prog: Program): (String, String) = {
    LLVMCompiler.run(prog, TMP_FILE, printDebug = false)
    val stdout = new StringBuilder

    val logger = ProcessLogger(
      (out: String) => stdout.append(out).append("\n"),
      (err: String) => System.err.println(err)
    )

    val exitCode = Process(Seq(s"./${TMP_FILE.toString}")).!(logger).toString
    TMP_FILE.toJava.delete()
    (exitCode, stdout.toString)
  }

  def interpret(prog: Program): (String, String) = {
    val stdout = new ByteArrayOutputStream()
    val ps = new PrintStream(stdout)

    Console.withOut(ps) {
      val (_, r) = Interpreter.run(prog)
      ps.flush()
      (r.toString, stdout.toString)
    }
  }
}
