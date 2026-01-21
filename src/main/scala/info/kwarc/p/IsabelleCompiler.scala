package info.kwarc.p

import info.kwarc.p.IsabelleCompiler.compileIsabelle


class IsabelleCompiler(tv: TheoryValue) {
  def compileToIsa(): Isa = compileIsabelle(tv)

}

object IsabelleCompiler {

  def compileIsabelle(tv: TheoryValue): Isa = {
    // first and only declaration must be a module, ensured by checker?
    assert(tv.decls.length == 1 && tv.decls.head.isInstanceOf[Module])
    compileDecl(tv.decls.head)
  }

  def findPackages(decls: IsaBody): String = {
    // todo: implement to find the packages for 'imports' statement
    "Main"
  }

  def compileDecl(decl: Declaration): Isa = {
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

  def compileDeclLocale(decl: Declaration): Isa = {
    decl match {
      case ed: ExprDecl => ed.tp match {
        case tp: ProofType => IsaLocaleAssumption(ed.name, compileType(tp))
        case tp => IsaLocaleFixes(ed.name, compileType(tp))
      }
      case td: TypeDecl => IsaLocaleTypeDummy()
    }
  }

  def compileDecls(decls: List[Declaration]): IsaBody = {
    IsaBody(decls.map(compileDecl))
  }

  def compileDeclsLocale(decls: List[Declaration]): IsaBody = {
    IsaBody(decls.map(compileDeclLocale))
  }

  def compileType(tp: Type): IsaType = {

    tp match {

      case utp: UnknownType => compileType(utp.container.tp)

      case FunType(ins, out) => IsaFunType(ins.variables.map(vd => compileType(vd.tp)), compileType(out))
      case ClosedRef(n) => IsaClosedRefType(n)

      case NumberType(true, false, false, false, false) => IsaIntType(tp.label)
      case BoolType => IsaBoolType(tp.label)

      case ProofType(formula) => IsaLocaleAssumptionType(compileExpr(formula))


      case null => null
    }
  }

  def compileExpr(expr: Expression): IsaExpr = {

    expr match {
      case IntValue(i) => IsaInt(i)
      case BoolValue(b) => IsaBool(b)

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

      case Equal => IsaEqual
    }
  }
}