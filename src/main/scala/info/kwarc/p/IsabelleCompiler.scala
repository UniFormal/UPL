package info.kwarc.p


/**
 * IsabelleCompiler translates the UPL internal representation into a surface-level syntax representation for Isabelle
 * that can be unparsed into type-checked Isabelle/HOL files (.thy file extension)
 *
 * The Compiler covers the whole UPL AST. It throws input errors for UPL constructs that are not yet implemented.
 *
 * The UPL AST is structured as follows:
 * ???: Program, Modifiers
 * Declarations: Modules, Include, TypeDecl, ExprDecl
 * Objects: Theory, Type, Expression
 * Ref (Expression, Type, Theory): OpenRef, ClosedRef, VarRef, AppliedRef, MaybeAppliedRef
 * OwnedObject: OwnedExpr, OwnedType, OwnedTheory
 * Theories: TheoryValue
 * Types: UnknownType, ClassType, ExprsOver, EmptyType, UnitType, BoolType, StringType,
 *        AnyType, ExceptionType, NumberType, IntervalType, FunType, ProdType, CollectionType, ProofType
 * Expressions: This, Instance, ExprOver, Eval, Lambda, Application, Tuple, Projection, CollectionValue, ListElem,
 *              Quantifier, Equality, Assert, UnitValue, BoolValue, NumberValue, ApproxReal, Rat, StringValue,
 *              BaseOperator, UndefinedValue
 * Standard programming language objects: EVarDecl, Assign, Block, IfThenElse, Match, MatchCase, For, While, Return,
 * Operators: (??? classes? e.g. PseudoInfixOperator)
 *            And, Or, Not, Implies, Plus, Minus, Times, Divide, Minimum, Maximum, Power, UMinus, Less, LessEq, Greater, GreaterEq
 *            Concat, In, Cons, Snoc, Equal, Inequal
 */

object IsabelleCompiler {

  def toIsabelleCode(tv: TheoryValue): String = {
    compileIsabelle(tv).toString
  }

  def compileIsabelle(tv: TheoryValue): IsaDecl = {
    // first and only declaration must be a module, is this ensured by the checker?
    assert(tv.decls.length == 1 && tv.decls.head.isInstanceOf[Module])
    compileDecl(tv.decls.head)
  }

  def packageImportsString(m: Module): String = {
    /** finds the packages for 'imports' statement
     * calls a Traverser method that indexes the packages
     * default output: "Main" (base package)
     * (rat || real || complex) ---> "Complex_Main" (base package)
     * bag                      ---> [base package] "HOL-Library.Multiset"
     * (not yet implemented) ulist ---> [base package] "HOL-Library.FSet"
     */
    IsabellePackageTraverser.importsString(GlobalContext.apply(m), m)
  }


  def compileDecl(decl: Declaration): IsaDecl = {
    decl match {
      case m: Module =>
        // closed/open - theory/locale
        if (!m.closed) {
          IsaTheory(m.name, compileDecls(m.df.decls), packageImportsString(m))
        }
        else {
          IsaLocale(m.name, compileDeclsLocale(m.df.decls))
        }
      //case ed: ExprDecl => IsaDefiniton(ed.name, compileType(ed.tp), compileExpr(ed.dfO.get))  // IsaExprDecl(name, type, definiens), compileType, compileExpr
      case ed: ExprDecl =>
        ed.tp match {
          case _: ProofType =>
            ed.dfO match {
              case Some(proof_term) => IsaTheorem(ed.name, compileType(ed.tp), compileExpr(proof_term))
              case None => IsaTheorem(ed.name, compileType(ed.tp), IsaEmptyProof())
            }
          case _ =>
            ed.dfO match {
              case Some(expr) => IsaExprDecl(ed.name, compileType(ed.tp), Some(compileExpr(expr)))
              case None => IsaExprDecl(ed.name, compileType(ed.tp), None)
            }
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
    /** Compiles all the case classes extending Type in the UPL AST:
     * UnknownType, ClassType, ExprsOver, EmptyType, UnitType, BoolType, StringType,
     * AnyType, ExceptionType, NumberType, IntervalType, FunType, ProdType, CollectionType, ProofType
     *
     * UPL might also pass type references:
     * Ref (Expression, Type, Theory): OpenRef, ClosedRef, VarRef, AppliedRef, MaybeAppliedRef
     */

    tp match {
      case utp: UnknownType => compileType(utp.container.tp)
      case ClassType(domain) => throw IError("ClassType not yet implemented. Zero test coverage.")
      case ExprsOver(scope, tp) => throw IError("ExprsOver not yet implemented. Zero test coverage.")
      case EmptyType => IsaEmptyType()
      case UnitType => IsaUnitType()
      case BoolType => IsaBoolType(tp.label)
      case StringType => IsaStringType()
      case AnyType => throw IError("AnyType not yet implemented. Zero test coverage.")
      case ExceptionType => throw IError("ExceptionType not yet implemented. Zero test coverage.")
      // todo: remove String argument in isabelle number types representation
      case NumberType(false, false, false, false, false) => IsaNatType("nat")
      case NumberType(true, false, false, false, false) => IsaIntType(tp.label)
      case NumberType(true, true, false, false, false) => IsaRatType("rat")
      case NumberType(true, true, true, false, false) => IsaComplexType("complex")
      case NumberType(true, true, false, true, true) => IsaRealType("real")
      case IntervalType(lower, upper) => throw IError("Isabelle does not have native interval types.")
      case FunType(ins, out) => IsaFunType(ins.variables.map(vd => compileType(vd.tp)), compileType(out))
      case ProdType(comps) => IsaProdType(comps.variables.reverseMap(vd => compileType(vd.tp)))
      case CollectionType(elem, kind) => kind match {
        case CollectionKind(false, false, true) => IsaOptionType(compileType(elem))
        case CollectionKind(false, false, false) => IsaListType(compileType(elem))
        case CollectionKind(true, true, false) => IsaSetType(compileType(elem))
        case CollectionKind(false, true, false) => IsaMultisetType(compileType(elem))
        case CollectionKind(true, false, false) => throw IError("ULists not yet implemented. Implement with distint property or as finite sets")
      }
      // todo: implement a flag that indicates inside or outside locale
      case ProofType(formula) => IsaProofType(compileExpr(formula))
      case ProofType(formula) => IsaLocaleAssumptionType(compileExpr(formula))
      // todo: references that are passed as types
      case OpenRef(path) => throw IError("OpenRef in compileType not yet implemented. Zero test coverage.")
      case ClosedRef(name) => IsaClosedRefType(name)
      case VarRef(name) => throw IError("VarRef in compileType not yet implemented. Zero test coverage.")
      // todo: applied references, newly added for polymorphism?
      //case AppliedRef(ref, args) =>

      case _ => throw IError("Encountered unknown type in compileType case-matching.")
    }
  }

  def compileExpr(expr: Expression): IsaExpr = {
    /** All the case classes extending Expression
     * Expressions: This, Instance, ExprOver, Eval, Lambda, Application, Tuple, Projection, CollectionValue, ListElem,
     * Quantifier, Equality, Assert, UnitValue, BoolValue, NumberValue, ApproxReal, Rat, StringValue,
     * BaseOperator, UndefinedValue
     *
     * Standard programming language objects: EVarDecl, Assign, Block, IfThenElse, Match, MatchCase, For, While, Return,
     *
     * Ref (Expression, Type, Theory): OpenRef, ClosedRef, VarRef, AppliedRef, MaybeAppliedRef
     */

    expr match {
      case Lambda(ins, body, mayReturn) => IsaLambda(ins.variables.map(compileExpr), compileExpr(body), true)
      case Application(fun, args) => IsaApplication(compileExpr(fun), compileExprs(args))
      case Tuple(comps) => IsaTuple(comps.map(compileExpr))
      case Projection(tuple, index) => throw IError("Projection in compileeExpr not yet implemented. Zero test coverage.")
      case CollectionValue(elems, kind) => kind match {
        case CollectionKind(false, false, true) => IsaOption(elems.map(compileExpr))
        case CollectionKind(false, false, false) => IsaList(elems.map(compileExpr))
        case CollectionKind(true, true, false) => IsaSet(elems.map(compileExpr))
        case CollectionKind(false, true, false) => IsaMultiset(elems.map(compileExpr))
        case CollectionKind(true, false, false) => throw IError("ULists not yet implemented. Implement with distinct property or as finite sets")
      }
      case ListElem(list, position) => throw IError("ListElem in compileExpr not yet implemented. Zero test coverage.")
      case Quantifier(univ, vars, body) => IsaQuantifier(univ, compileExprs(vars.variables), compileExpr(body))
      case Equality(positive, tp, left, right) => IsaEquality(positive, compileType(tp), compileExpr(left), compileExpr(right))
      case Assert(formula) => throw IError("Assert in compileeExpr not yet implemented. Zero test coverage.")
      case UnitValue => IsaUnit()
      case BoolValue(b) => IsaBool(b)
      // todo: convert Real to BigInt & compile to IsaInt, IsaReal; delete IsaNumber
      case NumberValue(tp, re, im) => tp match {
        case int => IsaNumber(re)
        case float => IsaNumber(re)
      }
      // todo: test IntValue, possibly redundant to NumberValue
      case IntValue(i) => IsaInt(i)
      // todo: ApproxReal? Rat?
      //case ApproxReal(value) => throw IError("ApproxReal in compileeExpr not yet implemented. Zero test coverage.")
      //case Rat(enu, deno) => throw IError("Rat in compileeExpr not yet implemented. Zero test coverage.")
      case StringValue(value) => IsaString(value)
      case BaseOperator(operator, tp) => IsaOperatorExpr(compileOp(operator), compileType(tp))
      // todo: look at UndefinedValue and test cases
      case uv: UndefinedValue if uv.label == "???" => IsaUndefinedProof(compileType(uv.tp))
      case UndefinedValue(tp) => throw IError("UndefinedValue for something other than proof terms not yet implemented")

      /** standard programming language objects */
      // todo: case EVarDecl after merge, what about TVarDecl?
      // todo: extend test cases, Block (in function definition), IfThenElse, Return
      case VarDecl(name, tp, dfO, mutable, output) => dfO match {
        case Some(value) => null
        case None => IsaVarDecl(name, compileType(tp))
      }
      case Assign(target, value) => throw IError("Assign in compileExpr not yet implemented. Zero test coverage.")
      case Block(exprs) => IsaBlock(compileExprs(exprs))
      case IfThenElse(cond, thn, els) => IsaIfThenElse(compileExpr(cond), compileExpr(thn), els.map(compileExpr))
      case Match(expr, cases, handler) => throw IError("Match in compileExpr not yet implemented. Zero test coverage.")
      case MatchCase(context, pattern, body) => throw IError("MatchCase in compileExpr not yet implemented. Zero test coverage.")
      case For(vd, range, body) => throw IError("For in compileExpr not yet implemented. Zero test coverage.")
      case While(cond, body) => throw IError("While in compileExpr not yet implemented. Zero test coverage.")
      case Return(exp, thrw) => IsaReturn(compileExpr(exp))

      /** references as expressions */
      // todo: OpenRef encountered in test42.p;
      case or: OpenRef => IsaVarRef(or.path.names.last)
      case ClosedRef(n) => IsaClosedRef(n)
      case VarRef(name) => IsaVarRef(name)
      // todo: applied references, newly added for polymorphism?
      //case AppliedRef(ref, args) =>

      case _ => throw IError("Encountered unknown expression in compileExpr case-matching.")
    }
  }

  def compileExprs(exprs: List[Expression]): List[IsaExpr] = {
    exprs.map(compileExpr)
  }

  def compileOp(op: Operator): IsaOperator = {
    // todo: all operators (case objects)
    /**
     * Operators: And, Or, Not, Implies, Plus, Minus, Times, Divide, Minimum, Maximum, Power, UMinus, Less, LessEq,
     * Greater, GreaterEq, Concat, In, Cons, Snoc, Equal, Inequal
     */
    op match {
      case And => IsaAnd
      case Or => IsaOr
      case Not => IsaNot
      case Implies => IsaImplies
      case Plus => IsaPlus
      case Minus => IsaMinus
      case Times => IsaTimes
      case Divide => IsaDivide
      case Minimum => IsaMinimum
      case Maximum => IsaMaximum
      // todo: how to distinguish between standard and real power, need to look up type of operands.
      case Power => IsaStandardPower
      case UMinus => IsaUMinus
      case Less => IsaLess
      case LessEq => IsaLessEq
      case Greater => IsaGreater
      case GreaterEq => IsaGreaterEq
      case Concat => IsaConcat
      case In => IsaIn
      case Cons => IsaCons
      case Snoc => IsaSnoc
      case Equal => IsaEqual
      case Inequal => IsaInequal
    }
  }

  // todo: test cases for blocks in function definitions
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


  def coerceIsaCollectionToIsaSet(expr: IsaExpr): IsaCollection = {
    assert(expr.isInstanceOf[IsaCollection])
    expr match {
      case IsaOption(elems) => IsaSet(elems)
      case IsaList(elems) => IsaSet(elems)
      case s: IsaSet => s
      case IsaMultiset(elems) => IsaSet(elems)
    }
  }
}