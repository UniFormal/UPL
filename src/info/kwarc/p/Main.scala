package info.kwarc.p

object Main {
  def main(args: Array[String]) = {
    val path = File(args(0))
    val src = File.read(path)
    val parser = new Parser(src)
    val decls = parser.parseDeclarations
    val main = if (args.length > 1) {
      val s = args(1)
      val parserM = new Parser(s)
      parserM.parseExpression(Context.empty)
    } else {
      UnitValue
    }
    val prog = Program(Vocabulary(decls), main)
    val progC = Checker.checkProgram(prog)
    val intp = new Interpreter(progC.voc)
    val res = intp.interpretExpression(progC.main)
    println(progC)
    println(res)
  }
}
