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

  def toIsabelleCode(tv: TheoryValue, gc: GlobalContext): String = {
    compileIsabelle(tv, gc).toString
  }

  def compileIsabelle(tv: TheoryValue, gc: GlobalContext): IsaDecl = {
    /** todo: support for multiple sequential (unnested) modules
    problem: modules are open; written to separate files and Isabelle theories; cross-references between theories in Isabelle?
     */
    // simple debug helper to verify declarations are in context
    debugPrintContext(gc)
    // first and only declaration must be a module
    assert(tv.decls.length == 1 && tv.decls.head.isInstanceOf[Module])
    /*val m: Module = tv.decls.head.asInstanceOf[Module]
    val gc: GlobalContext = GlobalContext.apply(m)*/
    compileToplevelModule(tv.decls.head, gc)
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

  def compileToplevelModule(decl: Declaration, gc: GlobalContext): IsaDecl = {
    decl match {
      case m: Module if !m.closed => IsaTheory(m.name, compileDecls(m.df.decls, gc), packageImportsString(m))
      case _ => throw IError("Must be a toplevel module.")
    }
  }


  def compileDecl(decl: Declaration, gc: GlobalContext): IsaDecl = {
    decl match {
      case m: Module =>
        // closed/open - theory/locale
        if (!m.closed) {
          //IsaTheory(m.name, compileDecls(m.df.decls), packageImportsString(m))
          throw IError("Nested modules can't be parsed to Isabelle theories.")
        }
        else {
          IsaLocale(m.name, compileDeclsLocale(m.df.decls, gc))
        }
      //case ed: ExprDecl => IsaDefiniton(ed.name, compileType(ed.tp), compileExpr(ed.dfO.get))  // IsaExprDecl(name, type, definiens), compileType, compileExpr
      case ed: ExprDecl =>
        ed.tp match {
          case _: ProofType =>
            ed.dfO match {
              case Some(proof_term) => IsaTheorem(ed.name, compileType(ed.tp, gc), compileExpr(proof_term, gc))
              case None => IsaTheorem(ed.name, compileType(ed.tp, gc), IsaEmptyProof())
            }
          case _ =>
            ed.dfO match {
              case Some(expr) => IsaExprDecl(ed.name, compileType(ed.tp, gc), Some(compileExpr(expr, gc)))
              case None => IsaExprDecl(ed.name, compileType(ed.tp, gc), None)
            }
        }
      case td: TypeDecl => td.dfO match {
        case Some(tp) => IsaTypeDef(td.name, Some(compileType(tp, gc)))
        case None => IsaTypeDef(td.name, None)
      }
    }
  }

  def compileDeclLocale(decl: Declaration, gc: GlobalContext): IsaDecl = {
    decl match {
      case ed: ExprDecl => ed.tp match {
        case tp: ProofType => IsaLocaleAssumption(ed.name, compileType(tp, gc))
        case tp => IsaLocaleFixes(ed.name, compileType(tp, gc))
      }
      case td: TypeDecl => IsaLocaleTypeDummy()
      case i: Include => IsaLocaleImport(i.dom.label)
    }
  }

  def compileDecls(decls: List[Declaration], gc: GlobalContext): IsaBody = {
    IsaBody(decls.map(d => compileDecl(d, gc)))
  }

  def compileDeclsLocale(decls: List[Declaration], gc: GlobalContext): IsaBody = {
    IsaBody(decls.map(compileDeclLocale(_, gc)), indent=true)
  }

  def compileType(tp: Type, gc: GlobalContext): IsaType = {
    /** Compiles all the case classes extending Type in the UPL AST:
     * UnknownType, ClassType, ExprsOver, EmptyType, UnitType, BoolType, StringType,
     * AnyType, ExceptionType, NumberType, IntervalType, FunType, ProdType, CollectionType, ProofType
     *
     * UPL might also pass type references:
     * Ref (Expression, Type, Theory): OpenRef, ClosedRef, VarRef, AppliedRef, MaybeAppliedRef
     */

    tp match {
      case utp: UnknownType => if (utp.container.tp == null) IsaUnknownType("null") else compileType(utp.container.tp, gc)
      case ClassType(domain) => throw IError("ClassType not yet implemented. Zero test coverage.")
      case ExprsOver(scope, tp) => throw IError("ExprsOver not yet implemented. Zero test coverage.")
      case EmptyType => IsaEmptyType()
      case UnitType => IsaUnitType()
      case BoolType => IsaBoolType(tp.label)
      case StringType => IsaStringType()
      case AnyType => IsaTypeVar("new_name")//throw IError("AnyType not yet implemented. Zero test coverage.")
      case ExceptionType => throw IError("ExceptionType not yet implemented. Zero test coverage.")
      // todo: remove String argument in isabelle number types representation
      case NumberType(false, false, false, false, false) => IsaNatType("nat")
      case NumberType(true, false, false, false, false) => IsaIntType(tp.label)
      case NumberType(true, true, false, false, false) => IsaRatType("rat")
      case NumberType(true, true, true, false, false) => IsaComplexType("complex")
      case NumberType(true, true, false, true, true) => IsaRealType("real")
      // todo: ratCF
      case NumberType(true, true, true, true, false) => IsaRealType("real")
      // todo: test080.p j produces NumberType ratCFI and Isabelle doesn't type-check
      case NumberType(true, true, true, true, true) => IsaRealType("real")
      case IntervalType(lower, upper) => throw IError("Isabelle does not have native interval types.")
      case FunType(ins, out) =>
        /** One input argument of type unit. basics009.p*/
        // todo: test with functions of zero input arguments
        if (ins.variables.size == 0)
          IsaFunType(List(IsaUnitType()), compileType(out, gc))
        else
          IsaFunType(ins.variables.map(vd => compileType(vd.tp, gc)), compileType(out, gc))
      case ProdType(comps) => IsaProdType(comps.variables.reverseMap(vd => compileType(vd.tp, gc)))
      case CollectionType(elem, kind) => kind match {
        case CollectionKind(false, false, true) => IsaOptionType(compileType(elem, gc))
        case CollectionKind(false, false, false) => IsaListType(compileType(elem, gc))
        case CollectionKind(true, true, false) => IsaSetType(compileType(elem, gc))
        case CollectionKind(false, true, false) => IsaMultisetType(compileType(elem, gc))
        case CollectionKind(true, false, false) => throw IError("ULists not yet implemented. Implement with distint property or as finite sets")
      }
      // todo: implement a flag that indicates inside or outside locale
      case ProofType(formula) => IsaProofType(compileExpr(formula, gc))
      case ProofType(formula) => IsaLocaleAssumptionType(compileExpr(formula, gc))
      // todo: references that are passed as types
      case OpenRef(path) => IsaOpenRefType(path.names.last)//throw IError("OpenRef in compileType not yet implemented. Zero test coverage.")
      case ClosedRef(name) => IsaClosedRefType(name)
      /** VarRef as a type variable, is it always the case? */
      case VarRef(name) => IsaTypeVar(name) //throw IError("VarRef in compileType not yet implemented. Zero test coverage.")
      // todo: applied references, newly added for polymorphism?
      //case AppliedRef(ref, args) =>

      case _ => throw IError("Encountered unknown type in compileType case-matching.")
    }
  }

  def compileExpr(expr: Expression, gc: GlobalContext): IsaExpr = {
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
      case Lambda(ins, body, mayReturn) =>
        // todo: if the body is a Lambda, it must be unparsed as a lambda expression (flagged with false)
        // todo: how to best handle? Here or in the toString method? We do it here
        /**
        val body_expr = compileExpr(body)
        body_expr match {
          case IsaLambda(args, body2, _, _) => IsaLambda(ins.variables.map(compileExpr), IsaLambda(args, body2, false), true)
          case _ => IsaLambda (ins.variables.map (compileExpr), body_expr, true)
        }
        */
        // todo: UPLs functions are all lambda expressions. Compile to Isabelle definitions with lambda expressions.
        /** Check for top-level pattern matching of function arguments in body of lambda-expression*/
        // todo: top-level pattern matching
        def topLevelMatchP(body: Expression): Boolean = {
          body match {
            case Lambda(ins, body, mayReturn) => topLevelMatchP(body)
            case Block(exprs) if (exprs.length == 1 & exprs.head.isInstanceOf[Match]) => true
            case _ => false
          }
        }
        if (topLevelMatchP(body)) {
          def ins_vars_flattened(body: Expression): List[Expression] = body match {
            case Lambda(ins, body, mayReturn) => ins.variables ++ ins_vars_flattened(body)
            case _ => List()
          }
          IsaFun(compileExprs(ins.variables ++ ins_vars_flattened(body), gc), compileTopLevelMatchFun(body, gc))
        } else if (ins.variables.size == 0) {
          /** In this case (basics009.p), one input argument of type unit which is value () */
          IsaLambda(List(IsaUnit()), compileExpr(body, gc))
        } else
          IsaLambda(compileExprs(ins.variables, gc), compileExpr(body, gc))
      case Application(fun, args) => IsaApplication(compileExpr(fun, gc), compileExprs(args, gc))
      case Tuple(comps) => IsaTuple(comps.map(compileExpr(_, gc)))
      case Projection(tuple, index) => IsaProjection(compileExpr(tuple, gc), index)
      case CollectionValue(elems, kind) => kind match {
        case CollectionKind(false, false, true) => IsaOption(elems.map(compileExpr(_, gc)))
        case CollectionKind(false, false, false) => IsaList(elems.map(compileExpr(_, gc)))
        case CollectionKind(true, true, false) => IsaSet(elems.map(compileExpr(_, gc)))
        case CollectionKind(false, true, false) => IsaMultiset(elems.map(compileExpr(_, gc)))
        case CollectionKind(true, false, false) => throw IError("ULists not yet implemented. Implement with distinct property or as finite sets")
      }
      case ListElem(list, position) => throw IError("ListElem in compileExpr not yet implemented. Zero test coverage.")
      case Quantifier(univ, vars, body) => IsaQuantifier(univ, compileExprs(vars.variables, gc), compileExpr(body, gc))
      case Equality(positive, tp, left, right) => IsaEquality(positive, compileType(tp, gc), compileExpr(left, gc), compileExpr(right, gc))
      case Assert(test, tp, expected) => throw IError("Assert in compileeExpr not yet implemented. Zero test coverage.")
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
      case BaseOperator(operator, tp) =>
        val isa_tp = compileType(tp, gc)
        IsaOperatorExpr(compileOp(operator, tp), compileType(tp, gc))
      // todo: look at UndefinedValue and test cases
      case uv: UndefinedValue if uv.label == "???" => IsaUndefinedProof(compileType(uv.tp, gc))
      case UndefinedValue(tp) => throw IError("UndefinedValue for something other than proof terms not yet implemented")

      /** standard programming language objects */
      // todo: case EVarDecl after merge, what about TVarDecl?
      // todo: extend test cases, Block (in function definition), IfThenElse, Return
      case EVarDecl(name, tp, dfO, mutable, output) => IsaVarDecl(name, compileType(tp, gc), dfO.map(compileExpr(_, gc)))
      //case TVarDecl
      case Assign(target, value) => throw IError("Assign in compileExpr not yet implemented. Zero test coverage.")
      case Block(exprs) => IsaBlock(compileExprs(exprs, gc))
      case IfThenElse(cond, thn, els) => IsaIfThenElse(compileExpr(cond, gc), compileExpr(thn, gc), els.map(compileExpr(_, gc)))
      case Match(expr, cases, handler) => throw IError("Match in compileExpr not yet implemented. Zero test coverage.")
      case MatchCase(context, pattern, body) => throw IError("MatchCase in compileExpr not yet implemented. Zero test coverage.")
      case For(vd, range, body) => throw IError("For in compileExpr not yet implemented. Zero test coverage.")
      case While(cond, body) => throw IError("While in compileExpr not yet implemented. Zero test coverage.")
      case Return(exp, thrw) => IsaReturn(compileExpr(exp, gc))

      /** references as expressions */
      // todo: OpenRef encountered in test42.p;
      case or: OpenRef =>
        val resolved = compileDecl(gc.lookupGlobal(or.path).getOrElse(throw IError("Global context lookup returns None.")), gc)
        IsaOpenRef(or.path.names.last, resolved)
      case ClosedRef(n) =>
        val resolved = compileDecl(gc.lookupRegional(n).getOrElse(throw IError("Regional context lookup returns None.")), gc)
        IsaClosedRef(n, resolved)
      case VarRef(name) =>
        //val resolved = compileVarDecl(gc.lookupLocal(name).getOrElse(throw IError("Local context lookup returns None.")), gc)
        val resolvedO = gc.lookupLocal(name).map(compileVarDecl(_, gc))
        IsaVarRef(name, resolvedO)
      // todo: applied references, newly added for polymorphism?
      //case AppliedRef(ref, args) =>

      case _ => throw IError("Encountered unknown expression in compileExpr case-matching.")
    }
  }

  def compileExprs(exprs: List[Expression], gc: GlobalContext): List[IsaExpr] = {
    exprs.map(compileExpr(_, gc))
  }

  def compileVarDecl(vd: VarDecl, gc: GlobalContext): IsaExpr = {
    /** Compile all case classes inheriting from VarDecl (Context.scala). */
    vd match {
      case EVarDecl(name, tp, dfO, mutable, output) => IsaVarDecl(name, compileType(tp, gc), dfO.map(compileExpr(_, gc)))
      case _ => throw IError("Unknown VarDecl.")
    }
  }

  def compileOp(op: Operator, tp: Type): IsaOperator = {
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
      case Divide => {
        val fun_tp = tp.asInstanceOf[FunType]
        if (fun_tp.ins.variables.forall(_.tp == NumberType.Int)
          & (fun_tp.out.label == "rat"))
        IsaFract
        else IsaFieldDivision
      }
      case Minimum => IsaMinimum
      case Maximum => IsaMaximum
      case Power =>
        val fun_tp = tp.asInstanceOf[FunType]
        assert(fun_tp.ins.variables.length == 2)
        // todo: FunType label is correct with exponent second; in variables list exponent is first (index 0)...
        fun_tp.ins.variables(0).tp match {
          case NumberType(_, false, false, _, _) => IsaStandardPower
          case NumberType(_, _, _, _, _) => IsaRealPower
          case _ => throw IError("Must be of NumberType.")
        }
      case UMinus => IsaUMinus
      case Less => IsaLess
      case LessEq => IsaLessEq
      case Greater => IsaGreater
      case GreaterEq => IsaGreaterEq
      case Concat => IsaConcat
      case In => IsaIn
      case Cons => IsaCons
      case Snoc => IsaSnoc
      /*case Equal => IsaEqual
      case Inequal => IsaInequal*/
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

  def compileTopLevelMatchFun(expr: Expression, gc: GlobalContext): IsaExpr = {
    expr match {
      case Lambda(ins, body, mayReturn) => compileTopLevelMatchFun(body, gc)
      case Block(exprs) =>
        assert(exprs.length == 1 & exprs.head.isInstanceOf[Match])
        compileTopLevelMatchFun(exprs.head, gc)
      case Match(expr, cases, handler) => IsaFunMatch(compileExpr(expr, gc), cases.map(compileTopLevelMatchFun(_, gc)))
      case MatchCase(context, pattern, body) => IsaFunCase(compileExpr(pattern, gc), compileExpr(body, gc))

    }
  }

  def debugPrintContext(gc: GlobalContext): Unit = {
    val voc = gc.voc
    println("Available declarations in context:")
    voc.decls.foreach { d =>
      d match {
        case m: Module =>
          println(s"  - Module: ${m.name}")
          // Traverse the module's declarations
          m.df.decls.foreach { decl =>
            decl match {
              case nd: NamedDeclaration => println(s"      - ${nd.name}")
              case _ => ()
            }
          }
        case nd: NamedDeclaration => println(s"  - ${nd.name}")
        case _ => ()
      }
    }
  }

  def compileName(name: String): String = {
    /** Compiles (variable) names. Reserved names (commands, keywords, reserved function names, ...) need to be escaped.
     * Collect all reserved names:
     *    commands: theory, begin, end, locale, definition, theorem, lemma, ...
     *    reserved function names: hd, tl, o, ...
     *    */
    "o'"
  }
}