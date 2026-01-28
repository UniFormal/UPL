package info.kwarc.p

import info.kwarc.p.IsabelleCompiler.compileIsabelle


class IsabelleCompiler(tv: TheoryValue) {
  def compileToIsa(): IsaDecl = compileIsabelle(tv)

}

object IsabelleCompiler {

  def compileIsabelle(tv: TheoryValue): IsaDecl = {
    // first and only declaration must be a module, ensured by checker?
    assert(tv.decls.length == 1 && tv.decls.head.isInstanceOf[Module])
    compileDecl(tv.decls.head)
  }

  def findPackages(decls: IsaBody): String = {
    // todo: implement to find the packages for 'imports' statement
    //if (rat || real || complex) "Complex_Main" else
    "Main"
  }

  def compileDecl(decl: Declaration): IsaDecl = {
    decl match {
      case m: Module =>
        // closed/open - theory/locale
        if (!m.closed) { IsaTheory(m.name, compileDecls(m.df.decls)) }
        else { IsaLocale(m.name, compileDeclsLocale(m.df.decls))}
      //case ed: ExprDecl => IsaDefiniton(ed.name, compileType(ed.tp), compileExpr(ed.dfO.get))  // IsaExprDecl(name, type, definiens), compileType, compileExpr
      case ed: ExprDecl => ed.dfO match {
        case Some(expr) => IsaExprDecl(ed.name, compileType(ed.tp), Some(compileExpr(expr)))
        case None => IsaExprDecl(ed.name, compileType(ed.tp), None)
      }
      case td: TypeDecl => td.dfO match {
        case Some(tp) => IsaTypeDef(td.name, Some(compileType(tp)))
        case None => IsaTypeDef(td.name, None)
      }
    }
  }

  def compileDeclLocale(decl: Declaration): IsaDecl = {
    decl match {
      case ed: ExprDecl => ed.tp match {
        case tp: ProofType => IsaLocaleAssumption(ed.name, compileType(tp))
        case tp => IsaLocaleFixes(ed.name, compileType(tp))
      }
      case td: TypeDecl => IsaLocaleTypeDummy()
      case i: Include => IsaLocaleImport(i.dom.label)
    }
  }

  def compileDecls(decls: List[Declaration]): IsaBody = {
    IsaBody(decls.map(compileDecl))
  }

  def compileDeclsLocale(decls: List[Declaration]): IsaBody = {
    IsaBody(decls.map(compileDeclLocale), true)
  }

  def compileType(tp: Type): IsaType = {

    tp match {

      case utp: UnknownType => compileType(utp.container.tp)

      case FunType(ins, out) => IsaFunType(ins.variables.map(vd => compileType(vd.tp)), compileType(out))
      case ClosedRef(n) => IsaClosedRefType(n)

      case NumberType(false, false, false, false, false) => IsaNatType("nat") // todo: remove String argument
      case NumberType(true, false, false, false, false) => IsaIntType(tp.label)
      case NumberType(true, true, false, false, false) => IsaRatType("rat")
      case NumberType(true, true, true, false, false) => IsaComplexType("complex")
      case NumberType(true, true, false, true, true) => IsaRealType("real")

      case BoolType => IsaBoolType(tp.label)
      case StringType => IsaStringType()
      case UnitType => IsaUnitType()

      case EmptyType => IsaEmptyType()

      case ProofType(formula) => IsaLocaleAssumptionType(compileExpr(formula))


      case null => null
    }
  }

  def compileExpr(expr: Expression): IsaExpr = {

    expr match {

      // numbers
      case NumberValue(tp, re, im) => tp match {
        case int => IsaNumber(re) // todo: convert Real to BigInt & compile to IsaInt, IsaReal; delete IsaNumber
        case float => IsaNumber(re)
      }
      case IntValue(i) => IsaInt(i)
      // bool & string
      case BoolValue(b) => IsaBool(b)
      case StringValue(value) => IsaString(value)
      // unit & any
      case UnitValue => IsaUnit()

      case Lambda(ins, body, mayReturn) => IsaLambda(ins.variables.map(compileExpr), compileExpr(body), true)
      case VarDecl(name, tp, dfO, mutable, output) => dfO match {
        case Some(value) => null
        case None => IsaVarDecl(name, compileType(tp))
      }
      case VarRef(name) => IsaVarRef(name)
      case ClosedRef(n) => IsaClosedRef(n)

      case Application(fun, args) => IsaApplication(compileExpr(fun), compileExprs(args))
      case BaseOperator(operator, tp) => IsaBaseOperator(compileOp(operator), compileType(tp))

      case Quantifier(univ, vars, body) => IsaQuantifier(univ, compileExprs(vars.variables), compileExpr(body))

    }

  }

  def compileExprs(exprs: List[Expression]): List[IsaExpr] = {
    exprs.map(compileExpr)
  }

  def compileOp(op: Operator): IsaOperator = {
    op match {
      case And => IsaAnd
      case Or => IsaOr
      case Not => IsaNot
      case Implies => IsaImplies

      case Less => IsaLess
      case LessEq => IsaLessEq

      case Plus => IsaPlus
      case Divide => IsaDivide

      case Equal => IsaEqual

      case UMinus => IsaUMinus
    }
  }
}