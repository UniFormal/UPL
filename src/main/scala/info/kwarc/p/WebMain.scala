package info.kwarc.p

import scala.scalajs.js.annotation._

object WebMain {
  @JSExportTopLevel("UPL")
  def run(input: String, mnS: String) : String = {
    try {
      val parserD = new Parser(SourceOrigin("anonymous"),input)
      val decls = parserD.parseDeclarations
      val parserM = new Parser(SourceOrigin("anonymous"),mnS)
      val mnE = parserM.parseExpression(PContext.empty)
      val prog = Program(decls,mnE)
      val progC = Checker.checkProgram(prog)
      val intp = new Interpreter(Module.anonymous(progC.voc))
      val res = intp.interpretExpression(progC.main)
      res.toString
    } catch {
      case e: PError => e.toString
    }
  }
}
