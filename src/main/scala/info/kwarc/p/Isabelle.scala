package info.kwarc.p

/**
 *
 * Code to translate from UPL code to Isabelle code
 * todo: think about refactoring into IsabelleCompiler.scala
 */

class Isabelle {

}

object Isabelle {

  def toIsabelleCode(tv: TheoryValue): String = {
    val isaComp = new IsabelleCompiler(tv)
    /**
    val isa = isaComp.compileToIsa()
    val s = isa.toString
    s
    */
    isaComp.compileToIsa().toString
  }

  def hol_parenthesize(hol_value: String):String = "\"" + hol_value + "\""

}