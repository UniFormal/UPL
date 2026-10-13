package info.kwarc.p.proving

import scala.util.parsing.combinator._

abstract class TPTP {

}

case class TPTPFile(decls: List[TPTPDecl]) extends TPTP {
  override def toString: String = decls.mkString("\n")
}

case class TPTPDecl(id: String, role: String, formula: TPTPFormula) extends TPTP {
  override def toString = s"thf($id,$role,$formula)."
}

case class TPTPBinaryOp(op: String, left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
  override def toString = s"($op @ $left @ $right)"
}


case class TPTPContext(decls: List[(String,TPTPFormula)]) extends TPTP
    {
        override def toString = {
            decls.map { case (v,t) => s"$v : $t"}.mkString(", ")
        }
    }


abstract class TPTPFormula extends TPTP

case class TPTPFunType(domain: TPTPFormula, range: TPTPFormula) extends TPTPFormula {
    override def toString = {
      def collect(tf: TPTPFormula): List[TPTPFormula] = tf match {
        case TPTPFunType(d, r) => d :: collect(r)
        case other => List(other)
      }
      collect(this).mkString("(", " > ", ")")
    }
}

case class TPTPTypeAssignment(ident: TPTPFormula, tpe: TPTPFormula) extends TPTPFormula {
    override def toString = s"$ident : $tpe"
}

case class TPTPConstant(name : String) extends TPTPFormula {
    override def toString = name
  }

case class TPTPVariable(name : String) extends TPTPFormula {
    override def toString = name.capitalize
  }

case class TPTPApply(fun: TPTPFormula, arg: TPTPFormula) extends TPTPFormula {
    override def toString = s"($fun @ $arg)"
  }

case class TPTPQuantifier(univ: Boolean, vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
  override def toString = {
    val q = if (univ) "!" else "?"
    s"($q[$vars]:$body)"
  }
}

case class TPTPTuple(elements: List[TPTPFormula]) extends TPTPFormula {
  override def toString: String = elements.mkString("<", ", ", ">") //Tuples not supported by leo-iii. needs workaround via fst, snd and more depending on scale
}

case class TPTPProductType(types: List[TPTPFormula]) extends TPTPFormula {
  override def toString: String = types.mkString(" * ")
}

case class TPTPLambda(vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(^ [$vars] : $body)"
}

case class TPTPConjunction(left: TPTPFormula, right: TPTPFormula) extends TPTPFormula
    {
        override def toString = s"($left & $right)"
    }

case class TPTPImplication( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString = s"($left => $right)"
}

case class TPTPEquivalent( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString = s"($left <=> $right)"
}

case class TPTPDisjunction( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
  override def toString = s"($left | $right)"
}

case class TPTPEquality(isEqual: Boolean, L: TPTPFormula, R: TPTPFormula) extends TPTPFormula {
    override def toString = {
        val e = if (isEqual) "=" else "!="
        s"($L $e $R)"
  }
}

case class TPTPNegation(body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(~ $body)"
}

case class TPTPInterpretedConstant(name: String) extends TPTPFormula {
    override def toString = if (name.startsWith("$")) name else s"$$$name"
}

case class TPTPChoice(isDefinite: Boolean, vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = {
      val cb = if (isDefinite) "@-" else "@+"
      s"($cb[$vars]:$body)"
  }
}

case class TPTPXor(left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString: String = s"($left <~> $right)"
}

case class TPTPIfThenElse(cond: TPTPFormula, thn: TPTPFormula, els: TPTPFormula) extends TPTPFormula {
    override def toString: String = s"$$ite($cond, $thn, $els)"
}

case class TPTPTypeQuantifier(vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(!> [$vars] : $body)"
}
