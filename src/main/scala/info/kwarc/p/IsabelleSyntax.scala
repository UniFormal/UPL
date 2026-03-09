package info.kwarc.p

/** Covers some subset of the UPL AST.
 * The covered AST nodes are translated into a surface-level syntax representation for Isabelle.
 * The other AST nodes throw IError*/

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
    case _: IsaFunType => "definition" //"fun"
    case _ => "definition"
  }

  override def toString = exprO match {
    /** case for top-level match in function body */
    case Some(IsaFun(ins, IsaFunMatch(expr, cases))) =>
      assert(tp.isInstanceOf[IsaFunType])
      assert(ins.length > 0)
      val ins_idx = ins.map(_.toString).indexOf(expr.toString)
      s"fun \"$name\" :: \"$tp\" where\n" +
      cases.map {
        case IsaFunCase(pattern, body) => "\"" + name + ins.updated(ins_idx, pattern).mkString(" ", " ", " ") + "= " + body.toString + "\""
        case _ => throw IError("Shouldn't be different to IsaFunCase")
      }.mkString("\n| ")
    case Some(IsaFun(ins, body)) => throw IError("body of IsaFun must be IsaFunMatch.")
    /** case for definition */
    // todo: only parenthesize complex types
    case Some(expr) => s"$isa_keyword \"$name\" :: \"$tp\" where\n" +
        s"  \"$name = $expr\""
    case None =>
      /** handle type empty & expression declarations without definiens */
      tp match {
        case IsaEmptyType() => throw IError("Can't translate empty type to Isabelle")
        case _ => s"$isa_keyword \"$name\" :: \"$tp\" where\n" + s"  \"$name = undefined\""
      }
  }
}

case class IsaBlock(exprs: List[IsaExpr]) extends IsaExpr {
  override def toString = throw IError("Block not yet implemented. Only in compileToplevelMatchFun.")
}

case class IsaIfThenElse(cond: IsaExpr, thn: IsaExpr, els: Option[IsaExpr]) extends IsaExpr {
  override def toString: String = "(" + s"if $cond then $thn " + (if (els.isDefined) s"else ${els.get}"  else "") + ")"
}

case class IsaReturn(expr: IsaExpr) extends IsaExpr {
  override def toString = expr.toString
}

case class IsaTypeDef(name: String, tpO: Option[IsaType]) extends IsaDecl {
  override def toString = tpO match {
    // todo: parenthesis?
    case Some(tp) => s"type_synonym $name = $tp"
    // todo: what about type declarations without definiens? (see test002.p)
    // todo: answer use keyword 'typedecl'.
    // todo: when to use keyword 'type_synonym' versus 'typedef'?
    case None => s"typedecl $name"
  }
}

case class IsaLocaleTypeDummy() extends IsaDecl {
  override def toString = ""
}

case class IsaLocaleFixes(name: String, tp: IsaType) extends IsaDecl {
  override def toString = s"fixes $name :: \"$tp\""
}

case class IsaLocaleAssumption(name: String, tp: IsaType) extends IsaDecl {
  override def toString = s"assumes $name: \"$tp\""
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

case class IsaNatType() extends IsaType {
  val name = "nat"
  override def toString: String = name
}

case class IsaIntType() extends IsaType {
  val name = "int"
  override def toString = name
}

case class IsaRatType() extends IsaType {
  val name = "rat"
  override def toString = name
}

case class IsaRealType() extends IsaType {
  val name = "real"
  override def toString = name
}

case class IsaComplexType() extends IsaType {
  val name = "complex"
  override def toString = name
}

case class IsaBoolType() extends IsaType {
  val name = "bool"
  override def toString = name
}

case class IsaStringType() extends IsaType {
  def name = "char list"
}

case class IsaEmptyType() extends IsaType {
  throw IError("Can't handle empty type")
  def name = "empty"
}


case class IsaFunType(ins: List[IsaType], out: IsaType, inner: Boolean = false) extends IsaType {
  def name: String = (ins :+ out).map(inner_funType).mkString(" => ")
  def inner_funType(tp: IsaType): IsaType = {
    tp match {
      case IsaFunType(ins, out, _) => IsaFunType(ins, out, true)
      case tp => tp
    }
  }
  override def toString: String = if (inner) {s"($name)"} else name
}

case class IsaOpenRefType(name: String) extends IsaType {

}

case class IsaClosedRefType(n: String) extends IsaType {
  def name: String = n
  //override def toString: String = name
}

case class IsaTypeVar(name: String) extends IsaType {
  override def toString: String = s"'$name"
}

case class IsaUnitType() extends IsaType {
  def name: String = "unit"
}

case class IsaProdType(comps: List[IsaType]) extends IsaType {
  override def name: String = comps.mkString(" \\<times> ")
}

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

case class IsaProofType(formula: IsaExpr) extends IsaType {
  def name = formula.toString
  override def toString = s"\"$formula\""
}

/*** Isabelle expressions **/

trait IsaExpr extends IsaDecl {
}

case class IsaTheorem(name: String, claim: IsaType, proof: IsaExpr) extends IsaExpr {
  override def toString = s"theorem $name: $claim\n$proof"
}

case class IsaEmptyProof() extends IsaExpr {
  override def toString = "apply(auto)\ndone"
}

case class IsaUndefinedProof(tp: IsaType) extends IsaExpr {
  override def toString = "apply(auto)\ndone"
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
  throw IError("cannot parse an empty value")
}

case class IsaUnit() extends IsaExpr {
  override def toString = "()"
}

case class IsaTuple(comps: List[IsaExpr]) extends IsaExpr {
  override def toString = comps.mkString("(", ",", ")")
}

case class IsaProjection(tuple: IsaExpr, index: Int) extends IsaExpr {
  override def toString = tuple match {
    case IsaTuple(comps) =>
      /** mapping follows a recursive "walk" down the right-hand side of the pairs.
       * For index $i < n$: Use fst after $i-1$ applications of snd.
       * For index $i = n$: Use $i-1$ applications of snd.
       */
      assert(1 <= index & index <= comps.length)
      if (index == comps.length) "snd (" * (index-1) + tuple.toString + ")" * (index -1)
      else "fst (" + "snd (" * (index-1) + tuple.toString + ")" * (index -1) + ")"
    case IsaOpenRef(name, resolved) => resolved match {
      case IsaExprDecl(name, tp, exprO) =>
        exprO.getOrElse(throw IError("Definiens is None.")) match {
          case IsaTuple(comps) =>
            assert(1 <= index & index <= comps.length)
            if (index == comps.length) "snd (" * (index-1) + tuple.toString + ")" * (index -1)
            else "fst (" + "snd (" * (index-1) + tuple.toString + ")" * (index -1) + ")"
          case _ => throw IError("Expected a tuple.")
        }
      case _ => throw IError("Expected ExprDecl.")
    }
    case _ => throw IError("Error in IsaProjection toString method. Expression is not a tuple.")
  }
}

sealed abstract class IsaCollection extends IsaExpr {
  val elems: List[IsaExpr]
}

case class IsaOption(elems: List[IsaExpr]) extends IsaCollection {
  override def toString = if (elems.isEmpty) {
    "None"
  } else if (elems.size == 1) {
    s"Some ${elems.head}"
  } else {
    throw IError("Option value contains more than one element")
  }
}

case class IsaList(elems: List[IsaExpr]) extends IsaCollection {
  override def toString = elems.mkString("[", ",", "]")
}

case class IsaListElem(list: IsaExpr, position: IsaExpr) extends IsaExpr {
  override def toString: String = s"$list ! $position"
}

case class IsaSet(elems: List[IsaExpr]) extends IsaCollection {
  override def toString = elems.mkString("{", ",", "}")
}

case class IsaMultiset(elems: List[IsaExpr]) extends IsaCollection {
  override def toString = elems.mkString("{#", ",", "#}")
}

case class IsaLambda(args: List[IsaExpr], body: IsaExpr, unparseAsFun: Boolean = false, nested: Boolean = false) extends IsaExpr {
  // probably body: IsaBody
  override def toString = if (!unparseAsFun) {
    // todo: flatten multiple lambdas, i.e. \x.\y.xy = \x y.xy
    "(\\<lambda>" + args.mkString(" ") + "." + " " + body.toString + ")"
  } else {
    body match {
      case IsaLambda(args2, body2, unparseAsFun2, nested2) => IsaLambda(args ::: args2, body2, unparseAsFun2, nested = true).toString
      case IsaVarRef(_, _) => args.map(_.toString).mkString(" ") + " = " + body.toString
      case IsaClosedRef(n, _) => n
      case app: IsaApplication => app.args.map(_.toString).mkString(" ") + " = " + app.toString
      //case IsaBlock(exprs) => IsabelleCompiler.compileBlockToFun(exprs)
    }
  }
}

case class IsaVarDecl(name: String, tp: IsaType, dfO: Option[IsaExpr]) extends IsaExpr {
  override def toString = name
}

/** trait IsaRef */

case class IsaOpenRef(name: String, resolved: IsaDecl) extends IsaExpr {
  override def toString = name
}

case class IsaClosedRef(n: String, resolved: IsaDecl) extends IsaExpr {
  override def toString = n
}

// todo: adapt inheritance hierarchy for VarDecl, mirror UPL hierarchy.
// todo: difference between Open, Closed, Var? Use tests to debug (Is VarRef used by tuple tests?)
// todo: VarRef used for function arguments (basics003.p)
case class IsaVarRef(name: String, resolvedO: Option[IsaDecl]) extends IsaExpr {
  override def toString = name
}

case class IsaApplication(fun: IsaExpr, args: List[IsaExpr]) extends IsaExpr {
  //assert(fun.isInstanceOf[IsaOperatorExpr])
  override def toString = fun match {
    case IsaOperatorExpr(op, tp) =>
      /** assert(op.arity.get == args.length) assertion fails for 1+2+3. In this case,
      fun is parsed as a ternary function while op remains of arity 2. */
      op match {
        case infOp: IsaInfixOperator =>
          /* assert(args.length == 2) assertion fails, see comment above */
          /** in operator in Isabelle only works for sets
           * todo: search for better solution regarding type coercions */
          if (op.symbol == "\\<in>") {
            // todo: subtyping, Isabelle has none, set inclusion only works for sets.
            val argsc = args.updated(1, IsabelleCompiler.coerceIsaCollectionToIsaSet(args(1)))
            "(" + argsc.mkString(" " + infOp.toString + " ") + ")"
          } else {
            "(" + args.mkString(" " + infOp.toString + " ") + ")"
          }
        case prefOp: IsaUnaryPrefixOperator =>
          assert(args.length == 1)
          "(" + prefOp.toString + " " + args.head.toString + ")"
        case binPrefOp: IsaBinaryPrefixOperator =>
          assert(args.length == 2)
          //"(" + binPrefOp.toString + " " + args.init.mkString(s" $binPrefOp ") + s" ${args.last})"
          "(" + binPrefOp.toString + " " + args.mkString(" ") + ")"
      }
    // todo figure out References, when open,closed,var? OpenRef in basics003 f5_multiarg application.
    case IsaOpenRef(name, _) => "(" + name + " " + args.map(_.toString).mkString(" ") + ")"
    case IsaClosedRef(n, _) => "(" + n + " " + args.map(_.toString).mkString(" ") + ")"
    case IsaVarRef(name, _) => "(" + name + " " + args.map(_.toString).mkString(" ") + ")"
    case _: IsaApplication =>
      val argss = args.mkString(" ")
      fun.toString + " " + args.mkString(" ")
    case _ => throw IError("unknown case in IsaApplication toString case-matching")
  }
}

case class IsaQuantifier(univ: Boolean, vars: List[IsaExpr], body: IsaExpr) extends IsaExpr {
  override def toString = "todo: quantifier string"
}

case class IsaEquality(positive: Boolean, tp: IsaType, left: IsaExpr, right: IsaExpr) extends IsaExpr {
  val op = if (positive) IsaEqual else IsaInequal
  override def toString = s"($left $op $right)"
}

/** Application expression composed of expressions
 * But operators are not expressions.
 **/

case class IsaOperatorExpr(operator: IsaOperator, tp: IsaType) extends IsaExpr {
  override def toString = "(" + operator.symbol + ":" + tp + ")"
  val label = operator.symbol
}

sealed abstract class IsaOperator {
  val symbol: String
  val length = symbol.length
  val arity: Option[Int]
}

sealed abstract class IsaInfixOperator(val symbol: String) extends IsaOperator {
  override def toString = s"$symbol"
  val arity = Some(2)
}

sealed abstract class IsaUnaryPrefixOperator(val symbol: String) extends IsaOperator {
  override def toString = s"$symbol"
  val arity = Some(1)
}

sealed abstract class IsaBinaryPrefixOperator(val symbol: String) extends IsaOperator {
  override def toString = s"$symbol"
  val arity = Some(2)
}

sealed trait IsaNumberOperator extends IsaOperator
sealed trait IsaCollectionOperator extends IsaOperator
sealed trait IsaArithmetic extends IsaNumberOperator

sealed trait IsaComparison extends IsaNumberOperator

sealed trait IsaConnective extends IsaOperator

case object IsaAnd extends IsaInfixOperator("\\<and>") with IsaConnective
case object IsaOr extends IsaInfixOperator("\\<or>") with IsaConnective
case object IsaNot extends IsaUnaryPrefixOperator("\\<not>") with IsaConnective
case object IsaImplies extends IsaInfixOperator("\\<longrightarrow>") with IsaConnective

case object IsaPlus extends IsaInfixOperator("+") with IsaArithmetic
case object IsaMinus extends IsaInfixOperator("-") with IsaArithmetic
case object IsaTimes extends IsaInfixOperator("*") with IsaArithmetic
case object IsaFieldDivision extends IsaInfixOperator("/") with IsaArithmetic
case object IsaDiv extends IsaInfixOperator("div") with IsaArithmetic
case object IsaFract extends IsaBinaryPrefixOperator("Fract") with IsaArithmetic
case object IsaStandardPower extends IsaInfixOperator("^") with IsaArithmetic
case object IsaRealPower extends IsaInfixOperator("powr") with IsaArithmetic

case object IsaMinimum extends IsaBinaryPrefixOperator("min") with IsaNumberOperator
case object IsaMaximum extends IsaBinaryPrefixOperator("max") with IsaNumberOperator
case object IsaUMinus extends IsaUnaryPrefixOperator("-") with IsaArithmetic

case object IsaLess extends IsaInfixOperator("<") with IsaComparison
case object IsaLessEq extends IsaInfixOperator("\\<le>") with IsaComparison
case object IsaGreater extends IsaInfixOperator(">") with IsaComparison
case object IsaGreaterEq extends IsaInfixOperator("\\<ge>") with IsaComparison

case object IsaConcat extends IsaInfixOperator("@") with IsaCollectionOperator
case object IsaIn extends IsaInfixOperator("\\<in>") with IsaCollectionOperator
case object IsaCons extends IsaInfixOperator("#") with IsaCollectionOperator
case object IsaSnoc extends IsaInfixOperator("@") with IsaCollectionOperator

case object IsaEqual extends IsaInfixOperator("=") with IsaComparison
case object IsaInequal extends IsaInfixOperator("\\<noteq>") with IsaComparison


case class IsaFun(ins: List[IsaExpr], body: IsaExpr) extends IsaExpr {
  override def toString: String = throw IError("not reached")
}

case class IsaFunMatch(expr: IsaExpr, cases: List[IsaExpr]) extends IsaExpr {
  override def toString: String = throw IError("not reached")
}

case class IsaFunCase(pattern: IsaExpr, body: IsaExpr) extends IsaExpr {
  override def toString: String = body.toString
}