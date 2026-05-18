package info.kwarc.p.proving

abstract class TPTP {

}

case class TPTPFile(decls: List[TPTPDecl]) extends TPTP

case class TPTPDecl(id: String, role: String, formula: TPTPFormula) extends TPTP {
  override def toString = s"th1($id,$role,$formula)."
}

abstract class TPTPFormula extends TPTP
case class Quantifier(univ: Boolean, vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
  override def toString = {
    val q = if (univ) "!" else "?"
    s"($q[$vars]:$body)"
  }
}

case class TPTPContext(decls: List[(String,TPTPFormula)]) extends TPTP