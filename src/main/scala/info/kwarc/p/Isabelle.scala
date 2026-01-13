package info.kwarc.p

/**
 *
 * Code to translate from UPL code to Isabelle code
 */

class Isabelle {

  //def toIsabelle(proj: Project): Isabelle {
  //}

}

object Isabelle {


  def translateCode(proj: Project): Unit = {

    // check the project files
    checkProj(proj)

    // translate TheoryValue in parsed field to a string (Isabelle source code) and write to files (.thy extension)
    Project.toIsabelleFiles(proj)
  }

  def checkProj(proj: Project): Unit = {
    val voc = proj.check(false)
  }

  def toIsabelleCode(tv: TheoryValue): String = {
    val isaComp = new IsabelleCompiler(tv)
    val isa = isaComp.compileToIsa()
    val s = isa.toString
    s
  }

}