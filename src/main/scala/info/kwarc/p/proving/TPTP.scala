package info.kwarc.p.proving

abstract class TPTP {

}

case class TPTPFile(decls: List[TPTPDecl]) extends TPTP {
  override def toString: String = decls.mkString("\n")
}

case class TPTPDecl(id: String, role: String, formula: TPTPFormula) extends TPTP {
  override def toString = s"th1($id,$role,$formula)."
}

case class TPTPContext(decls: List[(String,TPTPFormula)]) extends TPTP
    {
        override def toString = {
            decls.map { case (v,t) => s"$v : $t"}.mkString(", ")
        }
    }


abstract class TPTPFormula extends TPTP

case class FunType(domain: TPTPFormula, range: TPTPFormula) extends TPTPFormula {
    override def toString = s"($domain > $range)"
}

case class Constant(name : String) extends TPTPFormula {
    override def toString = name
  }

case class Variable(name : String) extends TPTPFormula {
    override def toString = name.capitalize
  }

case class Apply(fun: TPTPFormula, arg: TPTPFormula) extends TPTPFormula {
    override def toString = s"($fun @ $arg)"
  }

case class Quantifier(univ: Boolean, vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
  override def toString = {
    val q = if (univ) "!" else "?"
    s"($q[$vars]:$body)"
  }
}

case class Lambda(vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(^ [$vars] : $body)"
}

case class Conjunction(left: TPTPFormula, right: TPTPFormula) extends TPTPFormula
    {
        override def toString = s"($left & $right)"
    }

case class Implication( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString = s"($left => $right)"
}

case class Equivilant( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString = s"($left <=> $right)"
}

case class Disjunction( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
  override def toString = s"($left | $right)"
}

case class Equality(isEqual: Boolean, L: TPTPFormula, R: TPTPFormula) extends TPTPFormula {
    override def toString = {
        val e = if (isEqual) "=" else "!="
        s"($L $e $R)"
  }
}

case class Negation(body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(~ $body)"
}


