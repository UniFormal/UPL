package info.kwarc.p.proving

object Test {
  def main(args: Array[String]) = {
    // load project, find theory
    // for all declarations of the form c: |- F = ???, try to find a proof of conjecture F
    // collect all other declarations, make them axioms in TPTP
    // find ExprDecl(c, _, ProofType(F), Some(UndefinedValue(_)), _, _), make it a conjecture for F
  }
}
