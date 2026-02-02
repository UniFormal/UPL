package info.kwarc.p


class IsabelleCompiler(tv: TheoryValue, packString: String = "") {
  // todo: refactor methods from object IsabelleCompiler into this class?
  def compileToIsa(): IsaDecl = IsabelleCompiler.compileIsabelle(tv)
}

object IsabelleCompiler {

  def compileIsabelle(tv: TheoryValue): IsaDecl = {
    // first and only declaration must be a module, is this ensured by the checker?
    assert(tv.decls.length == 1 && tv.decls.head.isInstanceOf[Module])
    compileDecl(tv.decls.head)
  }

  def packageImportsString(m: Module): String = {
    /** finds the packages for 'imports' statement
    * calls a Traverser method that indexes the packages
    * default output: "Main" (base package)
    *   (rat || real || complex) ---> "Complex_Main" (base package)
    *   bag                      ---> [base package] "HOL-Library.Multiset"
    *   (not yet implemented) ulist ---> [base package] "HOL-Library.FSet"
    */
    IsabellePackageTraverser.importsString(GlobalContext.apply(m), m)
  }


  def compileDecl(decl: Declaration): IsaDecl = {
    decl match {
      case m: Module =>
        // closed/open - theory/locale
        if (!m.closed) { IsaTheory(m.name, compileDecls(m.df.decls), packageImportsString(m)) }
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

      case IntervalType(lower, upper) => throw IError("Isabelle does not have native interval types.")

      case ProdType(comps) => IsaProdType(comps.variables.reverseMap(vd => compileType(vd.tp)))

      case CollectionType(elem, kind) => kind match {
        case CollectionKind(false, false, true) => IsaOptionType(compileType(elem))
        case CollectionKind(false, false, false) => IsaListType(compileType(elem))
        case CollectionKind(true, true, false) => IsaSetType(compileType(elem))
        case CollectionKind(false, true, false) => IsaMultisetType(compileType(elem))
        case CollectionKind(true, false, false) => throw IError("ULists not yet implemented. Implement with distint property or as finite sets")
      }

      case ProofType(formula) => IsaLocaleAssumptionType(compileExpr(formula))

      case null => null
    }
  }

  def compileExpr(expr: Expression): IsaExpr = {

    expr match {

      // blocks, e.g. in function definition
      case b: Block => IsaBlock(compileExprs(b.exprs))
      case IfThenElse(cond, thn, els) => IsaIfThenElse(compileExpr(cond), compileExpr(thn), els.map(compileExpr))
      case Return(exp, thrw) => IsaReturn(compileExpr(exp))
      // numbers
      // todo: convert Real to BigInt & compile to IsaInt, IsaReal; delete IsaNumber
      case NumberValue(tp, re, im) => tp match {
        case int => IsaNumber(re)
        case float => IsaNumber(re)
      }
      case IntValue(i) => IsaInt(i)
      // bool & string
      case BoolValue(b) => IsaBool(b)
      case StringValue(value) => IsaString(value)
      // unit & any
      case UnitValue => IsaUnit()

      case Tuple(comps) => IsaTuple(comps.map(compileExpr))

      case CollectionValue(elems, kind) => kind match {
        case CollectionKind(false, false, true) => IsaOption(elems.map(compileExpr))
        case CollectionKind(false, false, false) => IsaList(elems.map(compileExpr))
        case CollectionKind(true, true, false) => IsaSet(elems.map(compileExpr))
        case CollectionKind(false, true, false) => IsaMultiset(elems.map(compileExpr))
        case CollectionKind(true, false, false) => throw IError("ULists not yet implemented. Implement with distint property or as finite sets")
      }

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
      case Minus => IsaMinus
      case Times => IsaTimes
      case Divide => IsaDivide

      case Equal => IsaEqual

      case UMinus => IsaUMinus

      case Cons => IsaCons
    }
  }

  def compileBlockToFun(fun_name: String, args: List[IsaExpr], tp: IsaType, blockexpr: IsaExpr): String = {
    assert(blockexpr.isInstanceOf[IsaBlock])
    blockexpr match {
      case b: IsaBlock => {
        val tl = b.exprs.tail
        b.exprs.head match {
          case ite: IsaIfThenElse => if (ite.thn.isInstanceOf[IsaReturn]) {
            s"  $fun_name " + args.mkString(" ") + " = " +
              s"(if ${ite.cond} then ${ite.thn} else " + tl.head.toString
          } else ite.toString
        }
      }
    }



  }
}