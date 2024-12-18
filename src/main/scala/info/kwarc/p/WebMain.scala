package info.kwarc.p

import scala.scalajs.js.annotation._

@JSExportTopLevel("UPL")
object WebMain {
  @JSExport
  def checkProgram(input: String) = {
    val parser = new Parser(SourceOrigin("anonymous"),input)
    val decls = parser.parseDeclarations
    val prog = Program(decls, UnitValue)
    Checker.checkProgram(prog)
  }

  @JSExport
  def runIn(prog: Program, expS: String) = {
    val parser = new Parser(SourceOrigin("anonymous"),expS)
    val mod = prog.toModule
    val exp = parser.parseExpression(PContext.empty)
    val (expC,expI) = Checker.inferExpression(GlobalContext(mod), exp)
    val intp = new Interpreter(mod)
    intp.interpretExpression(expC)
  }

  @JSExport
  def run(input: String, mnS: String) : String = {
    try {
      val prog = checkProgram(input)
      val r = runIn(prog, mnS)
      print(r)
    } catch {
      case e: PError => e.toString
    }
  }

  @JSExport
  def print(sf: SyntaxFragment) = sf.toString
}
