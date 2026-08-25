package info.kwarc.p.proving
import info.kwarc.p._
import info.kwarc.p.ValueFact.exprDeclAsExpr

object TPTPTranslator {
  def apply(thy: Theory, conj: Expression): TPTPFile = {
    val theoryDecls: List[TPTPDecl] = translateTheory(thy)
    val conjFormula: TPTPFormula = translateExpression(conj,null)
    val conjDecl = TPTPDecl("goal", "conjecture", conjFormula)
    TPTPFile(theoryDecls :+ conjDecl)
  }

  def translateTheory(thy: Theory): List[TPTPDecl] = {
    thy.decls.flatMap(d => translateDecl(d, null))  
  }
  //How does global context work? How does it affect the singular calls and what is translated when how and with what?

  def translateExpression(conj: Expression, gc: GlobalContext): TPTPFormula = conj match{
    case IntValue(i) => Constant(i.toString)
    case NumberValue(_,re,_) => Constant(re.toString)
    case BoolValue(b) => InterpretedConstant(if (b) "$true" else "$false")
    case VarRef(name) => Variable(name)
    case ClosedRef(name) => Constant(name)

    case Application(BaseOperator(And, _), List(l, r)) =>
      Conjunction(translateExpression(l, gc), translateExpression(r, gc))
    case Application(BaseOperator(Or, _), List(l, r)) =>
      Disjunction(translateExpression(l, gc), translateExpression(r, gc))
    case Application(BaseOperator(Implies, _), List(l, r)) =>
      Implication(translateExpression(l, gc), translateExpression(r, gc))
    case Application(BaseOperator(Not, _), List(body)) =>
      Negation(translateExpression(body, gc))     //could use if for these (Readability)

    case Application(fun, args) =>
      args.foldLeft(translateExpression(fun,gc)) {(acc, arg) => Apply(acc, translateExpression(arg, gc))} //General purpose application

    case IfThenElse(cond, thn, Some(els)) => TPTPIfThenElse(  //maybe rename all TPTP Syntax to TPTP<Name> to avoid confusion
      translateExpression(cond,gc),
      translateExpression(thn,gc),
      translateExpression(els,gc)
    )

    case Equality(positive, _, left, right) => 
      TPTPEquality(positive, translateExpression(left, gc), translateExpression(right, gc))

    case Quantifier(univ, vars, body) =>
      val ctx = TPTPContext(vars.variables.map(v => (v.name, translateType(v.tp, gc))))
      info.kwarc.p.proving.Quantifier(univ,ctx,translateExpression(body, gc))
    case Lambda(ins, body, _) =>
      val ctx = TPTPContext(ins.variables.map(v => (v.name, translateType(v.tp, gc))))
      LambdaTPTP(ctx, translateExpression(body, gc))
  }

  def translateDecl(decl: Declaration, gc: GlobalContext): List[TPTPDecl] = decl match{
    case module: Module =>
      module.decls.flatMap(d => translateDecl(d, gc))

    case ed: ExprDecl => 
      val typeDecl = TPTPDecl(
        s"${ed.name}_type", "type", TypeAssignment(Constant(ed.name), translateType(ed.tp, gc))
      )
      val axiomDecl = ed.dfO.map { expr =>
        TPTPDecl(s"${ed.name}_def", "axiom", TPTPEquality(true, Constant(ed.name), translateExpression(expr, gc)))
      }
      List(typeDecl) ++ axiomDecl.toList
    
    case td: TypeDecl =>
      List(TPTPDecl(s"${td.name}_type","type", TypeAssignment(Constant(td.name),InterpretedConstant("$tType"))))
    case _ => Nil
  }

  def translateType(typus: Type, gc: GlobalContext): TPTPFormula = typus match{
    case BoolType => InterpretedConstant("$o")
    case NumberType(true, false, _, _, _) => InterpretedConstant("$i")
    case UnitType => InterpretedConstant("$i")
    case FunType(ins,out) =>
      val domainType = ins.variables.map(vd => translateType(vd.tp, gc)).reduceLeft(info.kwarc.p.proving.FunType)
      info.kwarc.p.proving.FunType(domainType,translateType(out,gc))
    case ClosedRef(name) => Constant(name)
    case OpenRef(path) => Constant(path.names.last)

    case _ => InterpretedConstant("$i")
  }
}

