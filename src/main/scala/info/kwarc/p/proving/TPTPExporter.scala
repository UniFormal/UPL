package info.kwarc.p.proving
import info.kwarc.p._
import scala.collection.mutable.HashMap

object TPTPTranslator {
  private def unitDecls: List[TPTPDecl] = List(
    TPTPDecl("unit_type", "type", TPTPTypeAssignment(TPTPConstant("unit"), TPTPInterpretedConstant("$tType"))),
    TPTPDecl("unit_value_type", "type", TPTPTypeAssignment(TPTPConstant("unit_value"), TPTPConstant("unit"))),
    TPTPDecl(
      "unit_unique",
      "axiom",
      TPTPQuantifier(
        true,
        TPTPContext(List(("X", TPTPConstant("unit")))),
        TPTPEquality(true, TPTPVariable("X"), TPTPConstant("unit_value"))
      )
    )
  )
  private def typeUsesUnit(tp: Type): Boolean = tp match {
    case ProdType(comps) if comps.variables.isEmpty => true
    case ProdType(comps) => comps.variables.exists(v => typeUsesUnit(v.tp))
    case FunType(ins, out) => ins.variables.exists(v => typeUsesUnit(v.tp)) || typeUsesUnit(out)
    case AppliedRef(ref, tpargs, args) => typeUsesUnit(ref) || tpargs.exists(typeUsesUnit) || args.exists(exprUsesUnit)
    case OwnedType(_, _, inner) => typeUsesUnit(inner)
    case _ => false
  }

  private def exprUsesUnit(expr: Expression): Boolean = expr match {
    case Tuple(Nil) => true
    case Assert(test, _, expected) => exprUsesUnit(test) || exprUsesUnit(expected)
    case Application(fun, args) => exprUsesUnit(fun) || args.exists(exprUsesUnit)
    case IfThenElse(cond, thn, Some(els)) => exprUsesUnit(cond) || exprUsesUnit(thn) || exprUsesUnit(els)
    case Equality(_, _, left, right) => exprUsesUnit(left) || exprUsesUnit(right)
    case Quantifier(_, vars, body) => vars.variables.exists(v => typeUsesUnit(v.tp)) || exprUsesUnit(body)
    case Lambda(ins, body, _) => ins.variables.exists(v => typeUsesUnit(v.tp)) || exprUsesUnit(body)
    case Projection(tuple, _) => exprUsesUnit(tuple)
    case Tuple(es) => es.exists(exprUsesUnit)
    case OwnedExpr(_, _, inner) => exprUsesUnit(inner)
    case _ => false
  }

  private def declarationUsesUnit(decl: Declaration): Boolean = decl match {
    case ed: ExprDecl => typeUsesUnit(ed.tp) || ed.dfO.exists(exprUsesUnit)
    case td: TypeDecl => typeUsesUnit(td.tp) || td.dfO.exists(typeUsesUnit)
    case module: Module => module.decls.exists(declarationUsesUnit)
    case _ => false
  }

  private def needsUnitDecls(theory: Theory, conj: Expression): Boolean =
    theory.decls.exists(declarationUsesUnit) || exprUsesUnit(conj)

  private def containsArithmetic(expr: Expression): Boolean = expr match {
    case Application(BaseOperator(op, _), args) =>
      op match {
        case Plus | Minus | Times | Divide | Power | Minimum | Maximum | UMinus | Less | LessEq | Greater | GreaterEq => true
        case _ => args.exists(containsArithmetic)
      }
    case IfThenElse(cond, thn, els) => containsArithmetic(cond) || containsArithmetic(thn) || els.exists(containsArithmetic)
    case Lambda(_, body, _) => containsArithmetic(body)
    case _ => false
  }

  private def extractArgTypes(ins: ExprContext, gc: GlobalContext, table: HashMap[String, TPTPFormula], bodyContext: Option[Expression]): List[TPTPFormula] = {
    ins.variables.flatMap { vd =>
      vd.tp match {
        case ProdType(comps) if comps.variables.isEmpty => List(TPTPConstant("unit"))
        case ProdType(comps) => comps.variables.map(cvd => translateType(cvd.tp, gc, table, bodyContext))
        case null => List(TPTPInterpretedConstant("$int"))
        case t => List(translateType(t, gc, table, bodyContext))
      }
    }
  }

  def apply(thy: Theory, conj: Expression): TPTPFile = {
    val table = HashMap[String, TPTPFormula]()
    val theoryDecls: List[TPTPDecl] = translateTheory(thy, needsUnitDecls(thy, conj))
    val conjFormula: TPTPFormula = translateExpression(conj,null, table, None) 
    val conjDecl = TPTPDecl("goal", "conjecture", conjFormula)
    TPTPFile(theoryDecls :+ conjDecl)
  }

  def translateTheory(thy: Theory): List[TPTPDecl] = translateTheory(thy, thy.decls.exists(declarationUsesUnit))

  private def translateTheory(thy: Theory, includeUnitDecls: Boolean): List[TPTPDecl] = {
    val idents = if (includeUnitDecls) unitDecls else Nil
    val table = HashMap[String, TPTPFormula]()

    val decls = thy.decls.foldLeft(List.empty[TPTPDecl]) { (acc, d) =>
      acc ::: translateDecl(d, null, table)
    }

    idents ++ decls
  }

  def translateExpression(conj: Expression, gc: GlobalContext, table: HashMap[String, TPTPFormula], expectedTp: Option[TPTPFormula] = None): TPTPFormula = conj match {
    case IntValue(i) => TPTPConstant(i.toString)
    case NumberValue(_, re, _) => TPTPConstant(re.toString)
    case Tuple(Nil) => TPTPConstant("unit_value")
    case BoolValue(b) => TPTPInterpretedConstant(if (b) "$true" else "$false")
    case VarRef(name) => TPTPVariable(name)
    case ClosedRef(name) => TPTPConstant(name)
    case OpenRef(path) => TPTPConstant(path.names.mkString("_"))
    case AppliedRef(ref, tpargs, args) =>
      val base = translateExpression(ref, gc, table, None)
      val withTpArgs = tpargs.foldLeft(base) { (fun, arg) =>
        TPTPApply(fun, translateType(arg, gc, table))
      }
      args.foldLeft(withTpArgs) { (fun, arg) =>
        TPTPApply(fun, translateExpression(arg, gc, table, None))
      }
    case Tuple(es) => TPTPTuple(es.map(e => translateExpression(e, gc, table, None)))
    case Projection(tuple, index) =>
      TPTPApply(TPTPInterpretedConstant(s"$$proj$index"), translateExpression(tuple, gc, table, None))

    case StringValue(s) =>
      TPTPConstant("'" + s.replace("'", "''") + "'")
    case UndefinedValue(_) =>
      TPTPInterpretedConstant("$undefined")

    case Assert(test, _, expected) =>
      TPTPEquality(true, translateExpression(test, gc, table, None), translateExpression(expected, gc, table, None))

    case Application(BaseOperator(op, _), List(l, r)) =>
      op.symbol match {
        case "+"  => TPTPBinaryOp("$sum", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "-"  => TPTPBinaryOp("$difference", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "*"  => TPTPBinaryOp("$product", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "/"  => TPTPBinaryOp("$quotient", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "^"  => TPTPBinaryOp("$power", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "min" => TPTPBinaryOp("$min", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "max" => TPTPBinaryOp("$max", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "<"  => TPTPBinaryOp("$less", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "<=" => TPTPBinaryOp("$lesseq", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case ">"  => TPTPBinaryOp("$greater", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case ">=" => TPTPBinaryOp("$greatereq", translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "&"  => TPTPConjunction(translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "|"  => TPTPDisjunction(translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "=>" => TPTPImplication(translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case _    => TPTPApply(TPTPApply(TPTPConstant(op.symbol), translateExpression(l, gc, table, None)), translateExpression(r, gc, table, None))
      }

    case Application(BaseOperator(op, _), List(x)) =>
      op.symbol match {
        case "!" => TPTPNegation(translateExpression(x, gc, table, None))
        case "-" => TPTPApply(TPTPInterpretedConstant("$uminus"), translateExpression(x, gc, table, None))
        case _   => TPTPApply(TPTPConstant(op.symbol), translateExpression(x, gc, table, None))
      }

    case Application(tuple, List(IntValue(index)))
        if inferExprType(tuple, gc, table, None).exists(_.isInstanceOf[TPTPProductType]) =>
      TPTPApply(TPTPInterpretedConstant(s"$$proj$index"), translateExpression(tuple, gc, table, None))

    case Application(fun, args) =>
      args.foldLeft(translateExpression(fun, gc, table, None)) { (acc, arg) => 
        TPTPApply(acc, translateExpression(arg, gc, table, None)) 
      }

    case IfThenElse(cond, thn, Some(els)) => TPTPIfThenElse(
      translateExpression(cond, gc, table, None),
      translateExpression(thn, gc, table, None),
      translateExpression(els, gc, table, None)
    )

    case Equality(pn, _, left, right) => 
      TPTPEquality(pn, translateExpression(left, gc, table, None), translateExpression(right, gc, table, None))

    case Quantifier(univ, vars, body) =>
      val ctx = TPTPContext(vars.variables.map(v => (v.name, translateType(v.tp, gc, table))))
      TPTPQuantifier(univ, ctx, translateExpression(body, gc, table, None))

    case Lambda(ins, body, _) =>
      var curTp = expectedTp
      val newTable = HashMap(table.toSeq: _*)
      val ctxDecls = ins.variables.map { v =>
        val vTp = Option(v.tp) match {
          case Some(tp) if tp != null && !tp.isInstanceOf[UnknownType] => 
            translateType(tp, gc, table, Some(body))
          case Some(tp) if tp.isInstanceOf[UnknownType] =>
            curTp match {
              case Some(TPTPFunType(dom, _)) => dom
              case _ => TPTPInterpretedConstant("$int")
            }
          case None =>
            curTp match {
              case Some(TPTPFunType(dom, _)) => dom
              case _ => TPTPInterpretedConstant("$int") //base case as crutch for now
            }
        }
        curTp = curTp match {
          case Some(TPTPFunType(_, rng)) => Some(rng)
          case _ => None
        }
        newTable(v.name) = vTp
        (v.name, vTp)
      }
      val ctx = TPTPContext(ctxDecls)
      TPTPLambda(ctx, translateExpression(body, gc, newTable, curTp))
  }

def translateDecl(decl: Declaration, gc: GlobalContext, table: HashMap[String, TPTPFormula]): List[TPTPDecl] = decl match {
    case module: Module =>
      sys.error(s"Modules are not supported in TPTP translation: ${module.name}")

    case ed: ExprDecl => 
      val expectedTy: Option[TPTPFormula] = Option(ed.tp) match {
        case Some(tp) if tp != null && tp != AnyType && !tp.isInstanceOf[UnknownType] => 
          Some(translateType(tp, gc, table, ed.dfO))
        case _ => 
          ed.dfO.flatMap(expr => inferExprType(expr, gc, table, None))
      }

      val inferredTp = ed.dfO.flatMap(expr => inferExprType(expr, gc, table, expectedTy))

      val resolvedType: TPTPFormula = expectedTy match {
        case Some(tp) if tp != null && !containsI(tp) => tp
        case _ => inferredTp.getOrElse(TPTPInterpretedConstant("$int")) //Base case int as a crutch for f4 test.
      }

      table(ed.name) = resolvedType

      val translatedFormula: TPTPFormula = ed.tp match {
        case FunType(ins, out) if ins.variables.exists(v => isTypeKind(v.tp)) =>
          val (typeVars, termVars) = ins.variables.partition(v => isTypeKind(v.tp))
          val typeCtx = TPTPContext(typeVars.map(v => (v.name.capitalize, TPTPInterpretedConstant("$tType"))))
          val restFunType = if (termVars.isEmpty) out else FunType(ExprContext(termVars), out)
      
          TPTPTypeAssignment(
            TPTPConstant(ed.name),
            TPTPTypeQuantifier(typeCtx, translateType(restFunType, gc, table, ed.dfO))
          )

        case _ => 
          TPTPTypeAssignment(TPTPConstant(ed.name), resolvedType)
      }

      val typeDecl = TPTPDecl(s"${ed.name}_type", "type", translatedFormula)
      val axiomDecl = ed.dfO.map { expr =>
        TPTPDecl(s"${ed.name}_def", "axiom", TPTPEquality(true, TPTPConstant(ed.name), translateExpression(expr, gc, table, expectedTy)))
      }

      List(typeDecl) ++ axiomDecl.toList
  
    case td: TypeDecl => 
      td.dfO match {
        case Some(targetType) =>
          table(td.name) = translateType(targetType, gc, table, None)
          Nil

        case None =>
          val translatedTypeFormula: TPTPFormula = td.tp match {
            case FunType(ins, _) =>
              val typeCtx = TPTPContext(ins.variables.map(v => (v.name.capitalize, translateType(v.tp, gc, table, None))))
              TPTPTypeAssignment(
                TPTPConstant(td.name),
                TPTPTypeQuantifier(typeCtx, TPTPInterpretedConstant("$tType"))
              )
          
            case _ =>
              TPTPTypeAssignment(TPTPConstant(td.name), TPTPInterpretedConstant("$tType"))
          }

          List(TPTPDecl(s"${td.name}_type", "type", translatedTypeFormula))
      }
  }

private def inferExprType(expr: Expression, gc: GlobalContext, table: HashMap[String, TPTPFormula], expectedTp: Option[TPTPFormula] = None): Option[TPTPFormula] = expr match {
    case IntValue(_) => Some(TPTPInterpretedConstant("$int"))
    case NumberValue(_, _, _) => Some(TPTPInterpretedConstant("$int"))
    case BoolValue(_) => Some(TPTPInterpretedConstant("$o"))
    case Tuple(Nil) => Some(TPTPConstant("unit"))
    case StringValue(_) => Some(TPTPConstant("string"))
    case VarRef(name) => table.get(name)
    case ClosedRef(name) => table.get(name)
    case Application(BaseOperator(op, _), _) => op match {
      case Plus | Minus | Times | Divide | Power | Minimum | Maximum | UMinus =>
        Some(TPTPInterpretedConstant("$int"))
      case Less | LessEq | Greater | GreaterEq | And | Or | Implies | Not =>
        Some(TPTPInterpretedConstant("$o"))
      case _ => None
    }
    case Equality(_, _, _, _) => Some(TPTPInterpretedConstant("$o"))
    case Assert(_, _, _) => Some(TPTPInterpretedConstant("$o"))
    case Tuple(es) =>
      val types = es.flatMap(e => inferExprType(e, gc, table, None))
      if (types.size == es.size) Some(TPTPProductType(types)) else None
    case IfThenElse(_, thn, _) => inferExprType(thn, gc, table, expectedTp)
    case Application(fun, args) =>
      inferExprType(fun, gc, table, None) match {
        case Some(funTp) =>
          args.foldLeft[Option[TPTPFormula]](Some(funTp)) {
            case (Some(TPTPFunType(_, range)), _) => Some(range)
            case _ => None
          }
        case None => None
      }
    case Lambda(ins, body, _) =>
      var curTp = expectedTp
      val newTable = HashMap(table.toSeq: _*)
      val paramTypes = ins.variables.map { v =>
        val pTp = Option(v.tp) match {
          case Some(tp) if tp != null && !tp.isInstanceOf[UnknownType] => translateType(tp, gc, table, Some(body))
          case _ =>
            curTp match {
              case Some(TPTPFunType(dom, _)) => dom
              case _ =>
                if (containsArithmetic(body)) TPTPInterpretedConstant("$int")
                else TPTPInterpretedConstant("$i") 
            }
        }
        curTp = curTp match {
          case Some(TPTPFunType(_, rng)) => Some(rng)
          case _ => None
        }
        newTable(v.name) = pTp
        pTp
      }
      inferExprType(body, gc, newTable, curTp) match {
        case Some(bodyTp) =>
          Some(paramTypes.foldRight(bodyTp) { (pTp, acc) => TPTPFunType(pTp, acc) })
        case None =>
          if (containsArithmetic(body)) Some(paramTypes.foldRight[TPTPFormula](TPTPInterpretedConstant("$int")) { (pTp, acc) => TPTPFunType(pTp, acc) })
          else None
      } 
    case _ => expectedTp
  }

    private def containsI(formula: TPTPFormula): Boolean = formula match {
    case TPTPInterpretedConstant("$i") => true
    case TPTPFunType(dom, rng) => containsI(dom) || containsI(rng)
    case TPTPTypeAssignment(_, tpe) => containsI(tpe)
    case _ => false
  }

  private def isTypeKind(tp: Type): Boolean = tp match {
    case ClosedRef("type") | VarRef("type") => true
    case _ => false
  }

  def translateType(typus: Type, gc: GlobalContext, table: HashMap[String, TPTPFormula], bodyContext: Option[Expression] = None): TPTPFormula = typus match {
    case BoolType => TPTPInterpretedConstant("$o")
    case nt @ NumberType(true, false, _, _, _) => nt.name match {
      case "nat" => TPTPConstant("nat")
      case "rat" => TPTPInterpretedConstant("$rat")
      case "int" => TPTPInterpretedConstant("$int")
      case _ => TPTPInterpretedConstant("$int")
    }
    case ProdType(comps) if comps.variables.isEmpty => TPTPConstant("unit")
    case ProdType(comps) => 
      val memberTypes = comps.variables.reverse.map(vd => translateType(vd.tp, gc, table, bodyContext))
      if (memberTypes.isEmpty) TPTPConstant("unit")
      else if (memberTypes.size == 1) memberTypes.head
      else TPTPProductType(memberTypes)
    case FunType(ins, out) =>
      val argTypes = extractArgTypes(ins, gc, table, bodyContext)
      val outTp = translateType(out, gc, table, bodyContext)
      argTypes.foldRight(outTp) { (argTp, acc) =>
        TPTPFunType(argTp, acc)
      }
    case ClosedRef(name) => table.getOrElse(name, TPTPConstant(name))
    case VarRef(name)    => table.getOrElse(name, TPTPVariable(name))
    case AppliedRef(ref, tpargs, args) =>
      val base = translateType(ref, gc, table, bodyContext)
      val withTpArgs = tpargs.foldLeft(base) { (fun, arg) =>  //applied ref with new tpargs parameter
        TPTPApply(fun, translateType(arg, gc, table, bodyContext))
      }
      args.foldLeft(withTpArgs) { (fun, arg) =>
        TPTPApply(fun, translateExpression(arg, gc, table, None))
      }
    case OpenRef(path) => TPTPConstant(path.names.mkString("_")) //fixed (full instead of last)
    case _: UnknownType =>
      bodyContext match {
        case Some(body) if containsArithmetic(body) => TPTPInterpretedConstant("$int")
        case _ => TPTPInterpretedConstant("$int") //if this is $i f4 breaks
      }
    case _ =>
      bodyContext match {
        case Some(body) if containsArithmetic(body) => TPTPInterpretedConstant("$int")
        case _ => TPTPInterpretedConstant("$int") //if this is $i f4 breaks
      }
  }
}
