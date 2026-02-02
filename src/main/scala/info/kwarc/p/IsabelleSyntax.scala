package info.kwarc.p


/** Isabelle declarations */

abstract class IsaDecl {
  def toString: String
}

case class IsaTheory(name: String, decls: IsaBody, packImpsString: String) extends IsaDecl {
  override def toString = s"theory ${name}\n" +
    s"  imports " + packImpsString + "\n" +
    s"begin\n\n" +
    decls.toString +
    s"end"
}

case class IsaLocale(name: String, decls: IsaBody) extends IsaDecl {
  override def toString = s"locale $name =\n" +
    decls.toString
}

//case class IsaLocale

case class IsaBody(decls: List[IsaDecl], indent: Boolean = false) extends IsaDecl {
  override def toString =
    if (indent) {"  " + decls.mkString("\n  ") + "\n\n"} else {decls.mkString("\n") + "\n\n"}
}


/*** Isabelle commands
 * declarations associated with a particular keyword
 * e.g. definition, lemma, theorem, fun, ...
**/

/*
case class IsaDefiniton(name: String, tp: IsaType, exprO: Option[IsaExpr]) extends IsaDecl {
  override def toString = exprO match {
    case Some(expr) => s"definition $name :: $tp where\n" +
      s"  \"$name = $expr\"\n"
    case None => s"definition $name :: $tp\n"
  }
}
*/

case class IsaExprDecl(name: String, tp: IsaType, exprO: Option[IsaExpr]) extends IsaDecl {
  def isa_keyword: String = tp match {
    case _: IsaFunType => "fun"
    case _ => "definition"
  }
  /**
    def lhs: String = exprO.get match {
      case l: IsaLambda => s"$name " + l.argnames.mkString(" ")
      case _ => "ploblem"
    }
  */
  override def toString = exprO match {
    // todo: only parenthesize complex types
    case Some(expr) => s"$isa_keyword $name :: \"$tp\" where\n" +
      // todo: better solution for handling "=" in 'definition' versus 'fun'.
      {if (isa_keyword == "fun")
        {expr match {
        case lam: IsaLambda => if (lam.body.isInstanceOf[IsaBlock]) IsabelleCompiler.compileBlockToFun(name, lam.args, tp, lam.body)
          else(s"  \"$name $expr\"")
        }}
      else s"  \"$name = $expr\""}
    case None =>
      // todo: handle type empty & expression declarations without definiens
      // todo:
      if (tp.isInstanceOf[IsaEmptyType])
        /*"typedecl empty\n" +
          "definition e :: \"empty\" where\n  \"e = undefined\""
         */
        throw IError("Can't translate empty type to Isabelle")
      else
        s"$isa_keyword $name :: $tp where\n" +
        s"\"$name = undefined\""
  }
}

case class IsaBlock(exprs: List[IsaExpr]) extends IsaExpr {

}

case class IsaIfThenElse(cond: IsaExpr, thn: IsaExpr, els: Option[IsaExpr]) extends IsaExpr {
  override def toString: String = "(" + s"if $cond then $thn " + (if (els.isDefined) s"else ${els.get}"  else "") + ")"
}

case class IsaReturn(expr: IsaExpr) extends IsaExpr {
  override def toString = expr.toString
}

case class IsaTypeDef(name: String, tpO: Option[IsaType]) extends IsaDecl {
  override def toString = tpO match {
    case Some(tp) => s"type_synonym $name = $tp"
    // todo: what about type declarations without definiens? (see test3.p)
    // todo: answer use keyword 'typedecl'.
    // todo: when to use keyword 'type_synonym' versus 'typedef'
    case None => s"typedecl $name"
  }
}

case class IsaLocaleTypeDummy() extends IsaDecl {
  override def toString = ""
}

case class IsaLocaleFixes(name: String, tp: IsaType) extends IsaDecl {
  override def toString = s"fixes $name :: $tp"
}

case class IsaLocaleAssumption(name: String, tp: IsaType) extends IsaDecl {
  override def toString = s"assumes $name: $tp"
}

case class IsaLocaleImport(name: String) extends IsaDecl {
  override def toString = s"$name +"
}

/*** Isabelle types **/

// todo: implement all UPL types

trait IsaType extends IsaDecl {
  def name: String
  override def toString = s"$name"
}

case class IsaUnknownType(name: String) extends IsaType {

}

case class IsaNatType(name: String) extends IsaType {

}

case class IsaIntType(name: String) extends IsaType {
  override def toString = s"$name"
}

case class IsaRatType(name: String) extends IsaType {
  override def toString = s"$name"
}

case class IsaRealType(name: String) extends IsaType {
  override def toString = s"$name"
}

case class IsaComplexType(name: String) extends IsaType {
  override def toString = s"$name"
}

case class IsaBoolType(name: String) extends IsaType {
  override def toString = s"$name"
}

case class IsaStringType() extends IsaType {
  def name = "char list"
}

case class IsaEmptyType() extends IsaType {
  throw IError("Can't handle empty type")
  def name = "empty"
}


case class IsaFunType(ins: List[IsaType], out: IsaType, nested: Boolean = false) extends IsaType {
  def name: String = out match {
    // todo: possibly need this structure if only parenthesize complex types
    case IsaFunType(ins2, out2, _) =>
      if (nested) {
        ins.mkString(" => ") + " => " + IsaFunType(ins2, out2, nested = true)
      } else {
        ins.mkString(" => ") + " => " + IsaFunType(ins2, out2, nested = true)
      }
    case _ =>
      if (nested) {
        ins.mkString(" => ") + " => " + s"$out"
      } else {
        ins.mkString(" => ") + " => " + s"$out"
      }
  }
  override def toString: String = name
}

case class IsaClosedRefType(n: String) extends IsaType {
  def name: String = n
  //override def toString: String = name
}

case class IsaUnitType() extends IsaType {
  def name: String = "unit"
}

case class IsaProdType(comps: List[IsaType]) extends IsaType {
  override def name: String = comps.mkString(" \\<times> ")
}

// UPL collection type and kinds

case class IsaOptionType(elemType: IsaType) extends IsaType {
  override def name: String = s"$elemType option"
}

case class IsaListType(elemType: IsaType) extends IsaType {
  override def name: String = s"$elemType list"
}

case class IsaSetType(elemType: IsaType) extends IsaType {
  override def name: String = s"$elemType set"
}

case class IsaMultisetType(elemType: IsaType) extends IsaType {
  override def name: String = s"$elemType multiset"
}



case class IsaLocaleAssumptionType(formula: IsaExpr) extends IsaType {
  def name = formula.toString
  override def toString: String = formula match {
    case IsaQuantifier(univ, vars, body) => body.toString
    case _ => "IsaLocalAssumptionType toString match"
  }
}

/*** Isabelle expressions **/

trait IsaExpr extends IsaDecl {

}

case class IsaNumber(value: Real) extends IsaExpr {
  override def toString = value.toString
}

case class IsaNat(value: BigInt) extends IsaExpr {
  override def toString = value.toString
}

// inquire into BigInt
case class IsaInt(value: BigInt) extends IsaExpr {
  override def toString = value.toString
}
/*
case class IsaRat(value: Integral) extends IsaExpr {
  override def toString = value.toString
}
*/
case class IsaReal(value: Double) extends IsaExpr {
  override def toString = value.toString
}

case class IsaComplex(value: Integral[Double]) extends IsaExpr {
  override def toString = value.toString
}

case class IsaBool(value: Boolean) extends IsaExpr {
  override def toString = value.toString.head.toUpper + value.toString.tail
}

case class IsaString(value: String) extends IsaExpr {
  override def toString = s"''$value''"
}

case class IsaEmpty() extends IsaExpr {
  IError("cannot parse an empty value")
}

case class IsaUnit() extends IsaExpr {
  override def toString = "()"
}

case class IsaTuple(comps: List[IsaExpr]) extends IsaExpr {
  override def toString = comps.mkString("(", ",", ")")
}

case class IsaOption(elems: List[IsaExpr]) extends IsaExpr {
  override def toString = if (elems.isEmpty) {
    "None"
  } else if (elems.size == 1) {
    s"Some ${elems.head}"
  } else {
    throw IError("Option value contains more than one element")
  }
}

case class IsaList(elems: List[IsaExpr]) extends IsaExpr {
  override def toString = elems.mkString("[", ",", "]")
}

case class IsaSet(elems: List[IsaExpr]) extends IsaExpr {
  override def toString = elems.mkString("{", ",", "}")
}

case class IsaMultiset(elems: List[IsaExpr]) extends IsaExpr {
  override def toString = elems.mkString("{#", ",", "#}")
}




case class IsaLambda(args: List[IsaExpr], body: IsaExpr, unparseAsFun: Boolean = false, nested: Boolean = false) extends IsaExpr {
  // probably body: IsaBody
  override def toString = if (!unparseAsFun) {
    // todo: flatten multiple lambdas, i.e. \x.\y.xy = \x y.xy
    "= \\<lambda>" + args.mkString(" ") + "." + body.toString
  } else {
    body match {
      case IsaLambda(args2, body2, unparseAsFun2, nested2) => IsaLambda(args ::: args2, body2, unparseAsFun2, nested = true).toString
      case IsaVarRef(name2) => args.map(_.toString).mkString(" ") + " = " + body.toString
      // todo: implement IsaContexts to merge type and function definitions with closed references
      case IsaClosedRef(n) => n
      case app: IsaApplication => app.args.map(_.toString).mkString(" ") + " = " + app.toString
      //case IsaBlock(exprs) => IsabelleCompiler.compileBlockToFun(exprs)
    }
  }

}

case class IsaVarDecl(name: String, tp: IsaType) extends IsaExpr {
  // extend with definiens, mutable, output?
  // VarDecl inside Lambda
  override def toString = name

}

//case class IsaRef

case class IsaVarRef(name: String) extends IsaExpr {
  override def toString = name
}
case class IsaClosedRef(n: String) extends IsaExpr {
  override def toString = n
}

case class IsaApplication(fun: IsaExpr, args: List[IsaExpr]) extends IsaExpr {
  //assert(fun.isInstanceOf[IsaBaseOperator])
  override def toString = fun match {
    //case infOp: IsaInfixOperator => args.mkString(fun.toString)
    //case prefOp: IsaPrefixOperator => fun.toString + args.head.toString
    case IsaBaseOperator(op, tp) => op match {
      case infOp: IsaInfixOperator => "(" + args.mkString(" " + infOp.toString + " ") + ")"
      case prefOp: IsaPrefixOperator => "(" + prefOp.toString + " " + args.head.toString + ")"
    }
    case IsaClosedRef(n) => n + " " + args.map(_.toString).mkString(" ")
    case _ => "IsaApplication toString matching"
  }
}

case class IsaQuantifier(univ: Boolean, vars: List[IsaExpr], body: IsaExpr) extends IsaExpr {
  override def toString = "todo: quantifier string"
}

/** Application expression composed of expressions
 * But operators are not expressions.
 **/

case class IsaBaseOperator(operator: IsaOperator, tp: IsaType) extends IsaExpr {
  override def toString = "(" + operator.symbol + ":" + tp + ")"
  def label = operator.symbol
}

sealed abstract class IsaOperator {
  val symbol: String
  val length = symbol.length
}

sealed trait IsaGeneralInfixOperator extends IsaOperator {
  val symbol: String
  def arity = Some(2)
}

sealed abstract class IsaInfixOperator(val symbol: String) extends IsaGeneralInfixOperator {
  override def toString = s"$symbol"
}

sealed abstract class IsaPrefixOperator(val symbol: String) extends IsaOperator {
  override def toString = s"$symbol"
  def arity = Some(1)
}

sealed trait IsaNumberOperator extends IsaOperator

sealed trait IsaArithmetic extends IsaNumberOperator

sealed trait IsaComparison extends IsaNumberOperator

sealed trait IsaConnective extends IsaOperator

case object IsaPlus extends IsaInfixOperator("+") with IsaArithmetic

case object IsaMinus extends IsaInfixOperator("-") with IsaArithmetic

case object IsaTimes extends IsaInfixOperator("*") with IsaArithmetic

case object IsaDivide extends IsaInfixOperator("/") with IsaArithmetic

case object IsaUMinus extends IsaPrefixOperator("-") with IsaArithmetic

case object IsaLess extends IsaInfixOperator("<") with IsaComparison

case object IsaLessEq extends IsaInfixOperator("\\<le>") with IsaComparison

case object IsaAnd extends IsaInfixOperator("\\<and>") with IsaConnective

case object IsaOr extends IsaInfixOperator("\\<or>") with IsaConnective

case object IsaNot extends IsaPrefixOperator("\\<not>")

case object IsaImplies extends IsaInfixOperator("\\<longrightarrow>") with IsaConnective

case object IsaEqual extends IsaInfixOperator("=") with IsaComparison

case object IsaCons extends IsaInfixOperator("#")