package info.kwarc.p

import scala.scalajs.js.annotation._

@JSExportTopLevel("UPL")
@JSExportAll
object WebMain {
  val checker = new Checker(ErrorThrower)
  def checkProgram(input: String) = {
    val voc = Parser.text(SourceOrigin("anonymous"),input, ErrorThrower)
    val prog = Program(voc, UnitValue)
    checker.checkProgram(prog)
  }

  def runIn(prog: Program, expS: String) = {
    val parser = new Parser(SourceOrigin("anonymous"),expS, ErrorThrower)
    val exp = parser.parseExpression(PContext.empty)
    val (expC,expI) = checker.checkAndInferExpression(GlobalContext(prog.voc), exp)
    val intp = new Interpreter(prog.voc)
    intp.interpretExpression(expC)
  }

  def run(input: String, mnS: String) : String = {
    val prog = checkProgram(input)
    val r = runIn(prog, mnS)
    print(r)
  }

  def print(sf: SyntaxFragment) = sf.toString
}
