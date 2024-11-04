package info.kwarc.p

object Main {
  def main(args: Array[String]) = {
    val path = File(args(0))
    val src = File.read(path)
    val parser = new Parser(path, src)
    val decls = parser.parseDeclarations
    val main = if (args.length > 1) {
      val s = args(1)
      val parserM = new Parser(path, s)
      parserM.parseExpression(PContext.empty)
    } else {
      UnitValue
    }
    val prog = Program(decls, main)
    val progC = Checker.checkProgram(prog)
    val intp = new Interpreter(Module.anonymous(progC.voc))
    val res = intp.interpretExpression(progC.main)
    println(progC)
    println(res)
  }
}
