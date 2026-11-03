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

  private def natDecls: List[TPTPDecl] = List(
    TPTPDecl("nat_type", "type", TPTPTypeAssignment(TPTPConstant("nat"), TPTPInterpretedConstant("$tType"))),
    TPTPDecl("nat_def", "definition", TPTPEquality(true, TPTPConstant("nat"), TPTPInterpretedConstant("$int"))),
    TPTPDecl(
      "nat_nonnegative",
      "axiom",
      TPTPQuantifier(
        true, // universal
        TPTPContext(List(("N", TPTPConstant("nat")))),
        TPTPApply(TPTPApply(TPTPInterpretedConstant("$greatereq"), TPTPVariable("N")), TPTPConstant("0")) //should be switched out with zero and suc
      )
    )
  )

  private def typeUsesNat(tp: Type): Boolean = tp match {
    case nt @ NumberType(true, false, _, _, _) if nt.name == "nat" => true
    case ProdType(comps) => comps.variables.exists(v => typeUsesNat(v.tp))
    case FunType(ins, out) => ins.variables.exists(v => typeUsesNat(v.tp)) || typeUsesNat(out)
    case AppliedRef(ref, tpargs, args) =>
      typeUsesNat(ref) || tpargs.exists(typeUsesNat) || args.exists(exprUsesNat)
    case OwnedType(_, _, inner) => typeUsesNat(inner)
    case _ => false
  }

  private def exprUsesNat(expr: Expression): Boolean = expr match {
    case Assert(test, _, expected) => exprUsesNat(test) || exprUsesNat(expected)
    case Application(fun, args) => exprUsesNat(fun) || args.exists(exprUsesNat)
    case IfThenElse(cond, thn, els) => exprUsesNat(cond) || exprUsesNat(thn) || els.exists(exprUsesNat)
    case Equality(_, _, left, right) => exprUsesNat(left) || exprUsesNat(right)
    case Quantifier(_, vars, body) => Option(vars).exists(_.variables.exists(v => typeUsesNat(v.tp))) || exprUsesNat(body)
    case Lambda(ins, body, _) => ins.variables.exists(v => typeUsesNat(v.tp)) || exprUsesNat(body)
    case Projection(tuple, _) => exprUsesNat(tuple)
    case Tuple(es) => es.exists(exprUsesNat)
    case OwnedExpr(_, _, inner) => exprUsesNat(inner)
    case AppliedRef(ref, tpargs, args) => typeUsesNat(ref) || tpargs.exists(typeUsesNat) || args.exists(exprUsesNat)
    case ListElem(list, pos) => exprUsesNat(list) || exprUsesNat(pos)
    case Block(exprs) => exprs.exists(exprUsesNat)
    case Assign(target, value) => exprUsesNat(target) || exprUsesNat(value)
    case Return(exp, _) => exprUsesNat(exp)
    case _ => false
  }

  private def declarationUsesNat(decl: Declaration): Boolean = decl match {
    case ed: ExprDecl => typeUsesNat(ed.tp) || ed.dfO.exists(exprUsesNat)
    case td: TypeDecl => typeUsesNat(td.tp) || td.dfO.exists(typeUsesNat)
    case module: Module => module.decls.exists(declarationUsesNat)
    case _ => false
  }

  private def needsNatDecls(theory: Theory, conj: Expression): Boolean =
    theory.decls.exists(declarationUsesNat) || exprUsesNat(conj)

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
    case Quantifier(_, vars, body) => Option(vars).exists(_.variables.exists(v => typeUsesUnit(v.tp))) || exprUsesUnit(body)
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

  private case class InputGoal(scope: Option[String], formula: Expression)

  private def isInputGoal(decl: Declaration): Boolean = decl match {
    case ed: ExprDecl if ed.name == "goal" && ed.tp.isInstanceOf[ProofType] && ed.dfO.isEmpty => true
    case _ => false
  }

  private def extractInputGoal(thy: Theory): (Theory, Option[InputGoal]) = {
    val goals = scala.collection.mutable.ArrayBuffer.empty[InputGoal]

    def cleanTheory(tv: TheoryValue, scope: Option[String]): TheoryValue = {
      val remaining = tv.decls.flatMap {
        case ed: ExprDecl if isInputGoal(ed) =>
          goals += InputGoal(scope, ed.tp.asInstanceOf[ProofType].formula)
          Nil
        case module: Module =>
          List(module.copy(df = cleanTheory(module.df, Some(module.name))).copyFrom(module))
        case decl => List(decl)
      }
      TheoryValue(remaining).copyFrom(tv)
    }

    val cleaned = thy match {
      case tv: TheoryValue => cleanTheory(tv, None)
      case _ => thy
    }
    if (goals.lengthCompare(1) > 0)
      throw new IllegalArgumentException("Only one top-level or theory-scoped 'goal:--- ...' conjecture is supported")
    (cleaned, goals.headOption)
  }

  def apply(thy: Theory, conj: Expression): TPTPFile = {
    val (exportTheory, inputGoal) = extractInputGoal(thy)
    val effectiveConjecture = inputGoal.map(_.formula).getOrElse(conj)
    translatePrepared(exportTheory, effectiveConjecture, inputGoal)
  }

  def applyDirect(thy: Theory, conj: Expression): TPTPFile =
    translatePrepared(thy, conj, None)

  private def translatePrepared(exportTheory: Theory, effectiveConjecture: Expression, inputGoal: Option[InputGoal]): TPTPFile = {
    val table = HashMap[String, TPTPFormula]()
    val modules = collectTheoryModules(exportTheory)
    val theoryDecls: List[TPTPDecl] = translateTheory(exportTheory,needsUnitDecls(exportTheory, effectiveConjecture),needsNatDecls(exportTheory, effectiveConjecture),table)
    val conjectureTable = inputGoal.flatMap(_.scope).flatMap { scope =>
      modules.get(scope).map { module =>
        structureScopeTable(scope, module.df, modules, table)
      }
    }.getOrElse(table)
    val existingIds = theoryDecls.map(_.id).toSet
    val goalOwnedDecls = declareOwnedReferences(effectiveConjecture, conjectureTable, modules).filterNot(d => existingIds(d.id))
    val conjFormula: TPTPFormula = translateExpression(effectiveConjecture, null, conjectureTable, None)
    val goalScopeAxioms = inputGoal.flatMap(_.scope).toList.flatMap { scope =>
      modules.get(scope).toList.flatMap { module =>
        translateMatchingScopedGoalAxioms(scope, module.df, modules, theoryDecls, conjFormula)
      }
    }.filterNot(d => existingIds(d.id) || goalOwnedDecls.exists(_.id == d.id))

    val conjDecl = TPTPDecl("goal", "conjecture", conjFormula)
    TPTPFile(theoryDecls ++ goalOwnedDecls ++ goalScopeAxioms :+ conjDecl)
  }

  def translateTheory(thy: Theory): List[TPTPDecl] =
    translateTheory(thy, thy.decls.exists(declarationUsesUnit), thy.decls.exists(declarationUsesNat), HashMap[String, TPTPFormula]())

  private def translateTheory(thy: Theory, includeUnitDecls: Boolean, includeNatDecls: Boolean, table: HashMap[String, TPTPFormula]
  ): List[TPTPDecl] = {
    val idents = (if (includeUnitDecls) unitDecls else Nil) ++ (if (includeNatDecls) natDecls else Nil)
    val modules = collectTheoryModules(thy)

    val decls = thy.decls.foldLeft(List.empty[TPTPDecl]) { (acc, d) =>
      acc ::: translateDecl(d, null, table)
    }
    val structureDecls = translateStructureRefinements(thy, modules, table)
    val allDecls = idents ++ decls ++ structureDecls
    var positions = Map.empty[String, Int]
    val uniqueDecls = scala.collection.mutable.ArrayBuffer.empty[TPTPDecl]
    allDecls.foreach { d =>
      positions.get(d.id) match {
        case Some(i) => uniqueDecls(i) = d
        case None =>
          positions += (d.id -> uniqueDecls.length)
          uniqueDecls += d
      }
    }
    uniqueDecls.toList
  }

  private def collectTheoryModules(thy: Theory): Map[String, Module] = {
    val modules = HashMap[String, Module]()
    def collect(decls: List[Declaration]): Unit = decls.foreach {
      case module: Module =>
        modules(module.name) = module
        collect(module.decls)
      case _ => ()
    }
    collect(thy.decls)
    modules.toMap
  }

  private def lookupTheoryModule(path: Path, modules: Map[String, Module]): Option[Module] = {
    modules.get(path.names.mkString("_"))
      .orElse(path.names.lastOption.flatMap(modules.get))
  }

  private def theoryReferenceIdentity(theory: Theory): String = theory match {
    case PhysicalTheory(path, _) => s"physical:${path.names.mkString("_")}"
    case OpenRef(path) => s"open:${path.names.mkString("_")}"
    case OwnedTheory(owner, ownerDom, owned) =>
      val ownerName = owner match {
        case ClosedRef(name) => name
        case OpenRef(path) => path.names.mkString("_")
        case VarRef(name) => name
        case _ => owner.getClass.getSimpleName
      }
      s"owned:$ownerName:${ownerDom.getClass.getSimpleName}:${owned.getClass.getSimpleName}"
    case _: TheoryValue => "anonymous-theory"
    case other => s"theory:${other.getClass.getSimpleName}"
  }

  private def declarationIdentity(decl: Declaration): String = decl match {
    case module: Module => s"module:${module.name}"
    case Include(dom, _, _) => s"include:${theoryReferenceIdentity(dom)}"
    case named: NamedDeclaration => s"${named.kind}:${named.name}"
    case other => other.getClass.getSimpleName
  }

  private def structureIdentity(theory: Theory): String = theory match {
    case PhysicalTheory(path, refinements) =>
      s"physical:${path.names.mkString("_")}:${refinements.map(declarationIdentity).mkString("|")}"
    case OpenRef(path) => s"open:${path.names.mkString("_")}"
    case OwnedTheory(owner, ownerDom, owned) =>
      val ownerName = owner match {
        case ClosedRef(name) => name
        case OpenRef(path) => path.names.mkString("_")
        case VarRef(name) => name
        case _ => owner.getClass.getSimpleName
      }
      s"owned:$ownerName:${theoryReferenceIdentity(ownerDom)}:${theoryReferenceIdentity(owned)}"
    case tv: TheoryValue => s"value:${tv.decls.map(declarationIdentity).mkString("|")}"
    case other => s"theory:${other.getClass.getSimpleName}:${other.decls.map(declarationIdentity).mkString("|")}"
  }

  private def shallowExpressionIdentity(expr: Expression): String = expr match {
    case ClosedRef(name) => s"ref:$name"
    case OpenRef(path) => s"open:${path.names.mkString("_")}"
    case VarRef(name) => s"var:$name"
    case _: UndefinedValue => "undefined"
    case instance: Instance => s"instance:${theoryReferenceIdentity(instance.theory)}"
    case OwnedExpr(owner, _, inner) => s"owned(${shallowExpressionIdentity(owner)}.${shallowExpressionIdentity(inner)})"
    case Application(fun, args) => s"app(${shallowExpressionIdentity(fun)}:${args.map(shallowExpressionIdentity).mkString(",")})"
    case Equality(isEqual, _, left, right) =>
      s"equality:$isEqual:${shallowExpressionIdentity(left)}:${shallowExpressionIdentity(right)}"
    case Lambda(ins, body, _) =>
      s"lambda:${ins.variables.map(_.name).mkString(",")}:${body.getClass.getSimpleName}"
    case Tuple(es) => s"tuple:${es.map(shallowExpressionIdentity).mkString(",")}"
    case other => other.getClass.getSimpleName
  }

  private def theoryMembers(theory: Theory, modules: Map[String, Module], seen: Set[String] = Set.empty): List[(String, Declaration)] = {
    val identity = structureIdentity(theory)
    if (seen(identity)) return Nil
    val nextSeen = seen + identity

    def fromModule(module: Module, visitedModules: Set[String]): List[(String, Declaration)] = {
      if (visitedModules(module.name)) Nil
      else {
        val nextVisitedModules = visitedModules + module.name
        val visited = nextSeen ++ nextVisitedModules.map(name => s"module:$name")
        module.decls.flatMap {
          case Include(dom, _, _) => theoryMembers(dom, modules, visited)
          case nested: Module => List((module.name, nested))
          case decl => List((module.name, decl))
        }
      }
    }

    theory match {
      case PhysicalTheory(path, refinements) =>
        lookupTheoryModule(path, modules).toList.flatMap(m => fromModule(m, Set.empty)) :::
          refinements.map(decl => ("refinement", decl))
      case OpenRef(path) =>
        lookupTheoryModule(path, modules).toList.flatMap(m => fromModule(m, Set.empty))
      case OwnedTheory(_, _, inner) => theoryMembers(inner, modules, nextSeen)
      case tv: TheoryValue =>
        tv.decls.flatMap {
          case Include(dom, _, _) => theoryMembers(dom, modules, nextSeen)
          case decl => List(("refinement", decl))
        }
      case other =>
        other.decls.flatMap {
          case Include(dom, _, _) => theoryMembers(dom, modules, nextSeen)
          case decl => List(("refinement", decl))
        }
    }
  }

  private def structureDomain(tp: Type, modules: Map[String, Module]): Option[Theory] = tp match {
    case ClassType(domain) => Some(domain)
    case OwnedType(_, _, inner) => structureDomain(inner, modules)
    case ClosedRef(name) => modules.get(name).map(_.df)
    case OpenRef(path) => lookupTheoryModule(path, modules).map(_.df)
    case AppliedRef(ref, _, _) => structureDomain(ref, modules)
    case _ => None
  }

  private def qualifiedFieldName(ownerPath: String, fieldName: String): String =
    s"owned_${safeNamePart(ownerPath)}_${safeNamePart(fieldName)}"

  private def qualifiedAxiomName(ownerPath: String, sourceTheory: String, axiomName: String): String =
    if (safeNamePart(ownerPath) == safeNamePart(sourceTheory)) qualifiedFieldName(ownerPath, axiomName)
    else s"${qualifiedFieldName(ownerPath, sourceTheory)}_${safeNamePart(axiomName)}"

  private def isStructureValueType(tp: Type, table: HashMap[String, TPTPFormula]): Boolean = tp match {
    case ClassType(_) => true
    case OwnedType(_, _, inner) => isStructureValueType(inner, table)
    case ClosedRef(name) => table.get(name).contains(TPTPInterpretedConstant("$i"))
    case OpenRef(path) => table.get(path.names.mkString("_"))
      .orElse(path.names.lastOption.flatMap(table.get)).contains(TPTPInterpretedConstant("$i"))
    case AppliedRef(ref, _, _) => isStructureValueType(ref, table)
    case _ => false
  }

  private def structureScopeTable(ownerPath: String, domain: Theory, modules: Map[String, Module], parentTable: HashMap[String, TPTPFormula]): HashMap[String, TPTPFormula] = {
    val members = theoryMembers(domain, modules)
    val localTable = HashMap(parentTable.toSeq: _*)

    members.collect { case (_, td: TypeDecl) if td.dfO.isDefined => td }.foreach { td =>
      val aliasedType = translateType(td.dfO.get, null, localTable, None)
      localTable(td.name) = aliasedType
      localTable(typeAliasMarker(td.name)) = aliasedType
    }

    val fields = members.collect {
      case (_, field: ExprDecl) if !field.tp.isInstanceOf[ProofType] => field
    }.foldLeft(List.empty[ExprDecl]) { (acc, next) =>
      acc.filterNot(_.name == next.name) :+ next
    }

    fields.foreach { field =>
      val qualifiedName = qualifiedFieldName(ownerPath, field.name)
      val fieldType = structureDomain(field.tp, modules).map(_ => TPTPInterpretedConstant("$i"))
        .orElse(Option(field.tp).filter(tp => tp != null && tp != AnyType && !tp.isInstanceOf[UnknownType])
          .map(tp => translateType(tp, null, localTable, field.dfO)))
        .getOrElse(TPTPInterpretedConstant("$i"))
      localTable(field.name) = fieldType
      localTable(symbolMarker(field.name)) = TPTPConstant(qualifiedName)
      field.ntO.foreach { case Notation(_, symbol) => localTable(symbol) = TPTPConstant(qualifiedName) }
    }
    localTable
  }

  private def renameTPTPContext(context: TPTPContext, fromPrefix: String, toPrefix: String): TPTPContext = TPTPContext(context.decls.map { case (name, tp) =>
    (name, renameTPTPFormula(tp, fromPrefix, toPrefix))
  })

  private def renameTPTPFormula(formula: TPTPFormula, fromPrefix: String, toPrefix: String): TPTPFormula = formula match {
    case TPTPConstant(name) if name.startsWith(fromPrefix) =>
      TPTPConstant(toPrefix + name.substring(fromPrefix.length))
    case constant: TPTPConstant => constant
    case variable: TPTPVariable => variable
    case TPTPBinaryOp(op, left, right) => TPTPBinaryOp(op, renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPFunType(domain, range) => TPTPFunType(renameTPTPFormula(domain, fromPrefix, toPrefix), renameTPTPFormula(range, fromPrefix, toPrefix))
    case TPTPTypeAssignment(ident, tpe) => TPTPTypeAssignment(renameTPTPFormula(ident, fromPrefix, toPrefix), renameTPTPFormula(tpe, fromPrefix, toPrefix))
    case TPTPApply(fun, arg) => TPTPApply(renameTPTPFormula(fun, fromPrefix, toPrefix), renameTPTPFormula(arg, fromPrefix, toPrefix))
    case TPTPQuantifier(univ, vars, body) => TPTPQuantifier(univ, renameTPTPContext(vars, fromPrefix, toPrefix), renameTPTPFormula(body, fromPrefix, toPrefix))
    case TPTPTuple(elements) => TPTPTuple(elements.map(renameTPTPFormula(_, fromPrefix, toPrefix)))
    case TPTPProductType(types) => TPTPProductType(types.map(renameTPTPFormula(_, fromPrefix, toPrefix)))
    case TPTPLambda(vars, body) => TPTPLambda(renameTPTPContext(vars, fromPrefix, toPrefix), renameTPTPFormula(body, fromPrefix, toPrefix))
    case TPTPConjunction(left, right) => TPTPConjunction(renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPImplication(left, right) => TPTPImplication(renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPEquivalent(left, right) => TPTPEquivalent(renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPDisjunction(left, right) => TPTPDisjunction(renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPEquality(isEqual, left, right) => TPTPEquality(isEqual, renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPNegation(body) => TPTPNegation(renameTPTPFormula(body, fromPrefix, toPrefix))
    case TPTPChoice(isDefinite, vars, body) => TPTPChoice(isDefinite, renameTPTPContext(vars, fromPrefix, toPrefix), renameTPTPFormula(body, fromPrefix, toPrefix))
    case TPTPXor(left, right) => TPTPXor(renameTPTPFormula(left, fromPrefix, toPrefix), renameTPTPFormula(right, fromPrefix, toPrefix))
    case TPTPIfThenElse(cond, thn, els) => TPTPIfThenElse(renameTPTPFormula(cond, fromPrefix, toPrefix), renameTPTPFormula(thn, fromPrefix, toPrefix), renameTPTPFormula(els, fromPrefix, toPrefix))
    case TPTPTypeQuantifier(vars, body) => TPTPTypeQuantifier(renameTPTPContext(vars, fromPrefix, toPrefix), renameTPTPFormula(body, fromPrefix, toPrefix))
    case other => other
  }

  private def translateMatchingScopedGoalAxioms(ownerPath: String, domain: Theory, modules: Map[String, Module], theoryDecls: List[TPTPDecl], goalFormula: TPTPFormula): List[TPTPDecl] = {
    val targetPrefix = s"owned_${safeNamePart(ownerPath)}_"
    val includedSources = includedModuleNames(domain, modules)
      .filter(source => safeNamePart(source) != safeNamePart(ownerPath))

    val specialized = includedSources.flatMap { source =>
      val sourcePrefix = s"owned_${safeNamePart(source)}_"
      theoryDecls.filter(decl => decl.role == "axiom" && decl.id.startsWith(sourcePrefix)).flatMap { decl =>
        val formula = renameTPTPFormula(decl.formula, sourcePrefix, targetPrefix)
        if (formula == goalFormula) {
          val suffix = decl.id.substring(sourcePrefix.length)
          Some(TPTPDecl(
            s"${targetPrefix}inherited_${safeNamePart(source)}_$suffix",
            "axiom",
            formula
          ))
        } else None
      }
    }

    specialized.foldLeft(List.empty[TPTPDecl]) { (acc, decl) =>
      if (acc.exists(_.id == decl.id)) acc else acc :+ decl
    }
  }

  private def includedModuleNames(theory: Theory, modules: Map[String, Module]): List[String] = {
    val result = scala.collection.mutable.ArrayBuffer.empty[String]
    val pending = scala.collection.mutable.ArrayBuffer[Theory](theory)
    val seenTheories = scala.collection.mutable.HashSet.empty[String]
    val seenModules = scala.collection.mutable.HashSet.empty[String]

    while (pending.nonEmpty) {
      val current = pending.remove(pending.length - 1)
      val identity = structureIdentity(current)
      if (!seenTheories(identity)) {
        seenTheories += identity
        current match {
          case PhysicalTheory(path, _) =>
            lookupTheoryModule(path, modules).foreach { module =>
              if (!seenModules(module.name)) {
                seenModules += module.name
                result += module.name
                module.decls.collect { case Include(dom, _, _) => dom }.reverse.foreach(dom => pending += dom)
              }
            }
          case OpenRef(path) =>
            lookupTheoryModule(path, modules).foreach { module =>
              if (!seenModules(module.name)) {
                seenModules += module.name
                result += module.name
                module.decls.collect { case Include(dom, _, _) => dom }.reverse.foreach(dom => pending += dom)
              }
            }
          case ClosedRef(name) =>
            modules.get(name).foreach { module =>
              if (!seenModules(module.name)) {
                seenModules += module.name
                result += module.name
                module.decls.collect { case Include(dom, _, _) => dom }.reverse.foreach(dom => pending += dom)
              }
            }
          case OwnedTheory(_, _, inner) => pending += inner
          case other => other.decls.collect { case Include(dom, _, _) => dom }.reverse.foreach(dom => pending += dom)
        }
      }
    }
    result.toList
  }

  private def translateStructureRefinements(thy: Theory, modules: Map[String, Module], table: HashMap[String, TPTPFormula]): List[TPTPDecl] = {
    val roots = thy.decls.collect { case module: Module => module }
    roots.flatMap { module =>
      val structures = translateStructure(module.name, module.df, modules, table, Set.empty)
      structures
    }
  }

  private def translateStructure(ownerPath: String, domain: Theory, modules: Map[String, Module], parentTable: HashMap[String, TPTPFormula], visited: Set[String]): List[TPTPDecl] = {
    val identity = structureIdentity(domain)
    if (visited(identity)) return Nil
    val members = theoryMembers(domain, modules)
    val localTable = HashMap(parentTable.toSeq: _*)
    members.collect { case (_, td: TypeDecl) if td.dfO.isDefined => td }.foreach { td =>
      val aliasedType = translateType(td.dfO.get, null, localTable, None)
      localTable(td.name) = aliasedType
      localTable(typeAliasMarker(td.name)) = aliasedType
    }

    val structureFields = members.collect {
      case (source, field: ExprDecl)
          if !field.tp.isInstanceOf[ProofType] && structureDomain(field.tp, modules).isDefined =>
        (source, field, structureDomain(field.tp, modules).get)
    }.foldLeft(List.empty[(String, ExprDecl, Theory)]) { (acc, next) =>
      val key = (next._2.name, structureIdentity(next._3), next._2.dfO.map(shallowExpressionIdentity).getOrElse(""))
      if (acc.exists { old =>
        (old._2.name, structureIdentity(old._3), old._2.dfO.map(shallowExpressionIdentity).getOrElse("")) == key
      }) acc
      else acc :+ next
    }

    val structureObjects = structureFields.map { case (_, field, _) =>
      val qualifiedName = qualifiedFieldName(ownerPath, field.name)
      localTable(field.name) = TPTPInterpretedConstant("$i")
      localTable(symbolMarker(field.name)) = TPTPConstant(qualifiedName)
      TPTPDecl(s"${qualifiedName}_type", "type",
        TPTPTypeAssignment(TPTPConstant(qualifiedName), TPTPInterpretedConstant("$i")))
    }

    val ordinaryFields = members.collect {
      case (source, field: ExprDecl)
          if !field.tp.isInstanceOf[ProofType] && structureDomain(field.tp, modules).isEmpty =>
        (source, field)
    }.foldLeft(List.empty[(String, ExprDecl)]) { (acc, next) =>
      acc.filterNot(_._2.name == next._2.name) :+ next
    }

    val typedFields = ordinaryFields.map { case (source, field) =>
      val qualifiedName = qualifiedFieldName(ownerPath, field.name)
      val fieldType = Option(field.tp)
        .filter(tp => tp != null && tp != AnyType && !tp.isInstanceOf[UnknownType])
        .map(tp => translateType(tp, null, localTable, field.dfO))
        .orElse(field.dfO.filterNot(containsInstance).filterNot(containsUndefined)
          .flatMap(expr => inferExprType(expr, null, localTable, None)))
        .getOrElse(TPTPInterpretedConstant("$i"))
      localTable(field.name) = fieldType
      localTable(symbolMarker(field.name)) = TPTPConstant(qualifiedName)
      field.ntO.foreach { case Notation(_, symbol) => localTable(symbol) = TPTPConstant(qualifiedName) }
      (source, field, qualifiedName, fieldType)
    }

    val fieldTypes = typedFields.map { case (_, _, qualifiedName, fieldType) =>
      TPTPDecl(s"${qualifiedName}_type", "type",
        TPTPTypeAssignment(TPTPConstant(qualifiedName), fieldType))
    }

    val fieldDefinitions = typedFields.flatMap { case (_, field, qualifiedName, fieldType) =>
      field.dfO.filterNot(containsInstance).filterNot(containsUndefined).map { expr =>
        TPTPDecl(s"${qualifiedName}_def", "axiom",
          TPTPEquality(true, TPTPConstant(qualifiedName), translateExpression(expr, null, localTable, Some(fieldType))))
      }
    }

    val specializedAxioms = members.flatMap {
      case (source, field: ExprDecl) if field.tp.isInstanceOf[ProofType] && field.dfO.isEmpty =>
        val formula = field.tp.asInstanceOf[ProofType].formula
        val axiomId = qualifiedAxiomName(ownerPath, source, field.name)
        val ownedDecls = declareOwnedReferences(formula, localTable, modules)
        ownedDecls :+ TPTPDecl(axiomId, "axiom", translateExpression(formula, null, localTable, None))

      case _ => Nil
    }

    val nestedInstances = structureFields.flatMap { case (_, field, _) =>
      field.dfO.collect {
        case instance: Instance =>
          translateInstanceFields(s"${ownerPath}_${field.name}", instance, null, localTable)
      }.getOrElse(Nil)
    }

    val nestedStructures = structureFields.flatMap { case (_, field, childDomain) =>
      translateStructure(s"${ownerPath}_${field.name}", childDomain, modules, localTable, visited + identity)
    }

    structureObjects ++ fieldTypes ++ fieldDefinitions ++ specializedAxioms ++ nestedInstances ++ nestedStructures
  }

private def variableMarker(name: String): String = s"__tptp_bound_var__:$name"
  private def symbolMarker(name: String): String = s"__tptp_symbol_alias__:$name"
  private def typeAliasMarker(name: String): String = s"__tptp_type_alias__:$name"

  private def normalizeInfixExpression(expr: Expression): Expression = {
    case class InfixNode(app: Application, base: BaseOperator, left: Expression, right: Expression)

    def infixNode(e: Expression): Option[InfixNode] = e match {
      case app @ Application(base @ BaseOperator(op, _), List(left, right))
          if op.fixity.isInstanceOf[Infix] => Some(InfixNode(app, base, left, right))
      case _ => None
    }

    def isParenthesized(node: InfixNode): Boolean = {
      val appLoc = node.app.loc
      val leftLoc = node.left.loc
      val rightLoc = node.right.loc
      appLoc != null && leftLoc != null && rightLoc != null &&
        (appLoc.from < leftLoc.from || appLoc.to > rightLoc.to)
    }

    def fallbackPrecedence(base: BaseOperator): Int = base.operator.symbol match {
      case "=>" | "<=>" => 1
      case "|" | "<~>" => 2
      case "&" => 3
      case "==" | "!=" | "=" | "<" | "<=" | ">" | ">=" => 4
      case "+" | "-" => 6
      case "*" | "/" | "^" => 7
      case _ => 5 
    }

    def shouldReduce(top: BaseOperator, incoming: BaseOperator): Boolean = {
      val topExplicit = top.operator match {
        case p: PseudoOperator => Some(p.precedence)
        case _ => None
      }
      val incomingExplicit = incoming.operator match {
        case p: PseudoOperator => Some(p.precedence)
        case _ => None
      }

      (topExplicit, incomingExplicit) match {
        case (Some(a), Some(b)) if a != b => a < b
        case _ =>
          val topRank = fallbackPrecedence(top)
          val incomingRank = fallbackPrecedence(incoming)
          if (topRank == incomingRank) {
            top.operator.symbol != "=>" || incoming.operator.symbol != "=>"
          } else topRank > incomingRank
      }
    }

    val operands = scala.collection.mutable.ArrayBuffer.empty[Expression]
    val operators = scala.collection.mutable.ArrayBuffer.empty[BaseOperator]

    def flatten(e: Expression, root: Boolean): Unit = infixNode(e) match {
      case Some(node) if root || !isParenthesized(node) =>
        flatten(node.left, root = false)
        operators += node.base
        flatten(node.right, root = false)
      case _ => operands += e
    }

    flatten(expr, root = true)
    if (operators.length < 2 || operands.length != operators.length + 1) expr
    else {
      val values = scala.collection.mutable.ArrayBuffer.empty[Expression]
      val pending = scala.collection.mutable.ArrayBuffer.empty[BaseOperator]

      def reduceTop(): Unit = {
        val op = pending.remove(pending.length - 1)
        val right = values.remove(values.length - 1)
        val left = values.remove(values.length - 1)
        values += Application(op, List(left, right))
      }

      operands.indices.foreach { i =>
        values += operands(i)
        if (i < operators.length) {
          val incoming = operators(i)
          while (pending.nonEmpty && shouldReduce(pending.last, incoming)) reduceTop()
          pending += incoming
        }
      }
      while (pending.nonEmpty) reduceTop()
      values.last
    }
  }

  def translateExpression(conj: Expression, gc: GlobalContext, table: HashMap[String, TPTPFormula], expectedTp: Option[TPTPFormula] = None): TPTPFormula = normalizeInfixExpression(conj) match {
    case IntValue(i) => TPTPConstant(i.toString)
    case NumberValue(_, re, _) => TPTPConstant(re.toString)
    case Tuple(Nil) => TPTPConstant("unit_value")
    case BoolValue(b) => TPTPInterpretedConstant(if (b) "$true" else "$false")
    case VarRef(name) => TPTPVariable(name)
    case ClosedRef(name) => table.get(variableMarker(name)).collect {
      case variable: TPTPVariable => variable
    }.orElse(table.get(symbolMarker(name)).collect {
      case constant: TPTPConstant => constant
    }).getOrElse(TPTPConstant(name))
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
    case Application(outerBase @ BaseOperator(outerOp, _), List(
          Application(BaseOperator(andOp, _), List(
            innerApp @ Application(BaseOperator(innerOp, _), List(a, b)), c)), d))
        if outerOp.fixity.isInstanceOf[Infix] && andOp.symbol == "&" &&
          innerOp.fixity.isInstanceOf[Infix] && outerOp.symbol == innerOp.symbol =>
      TPTPConjunction(
        translateExpression(innerApp, gc, table, None),
        translateExpression(Application(outerBase, List(c, d)), gc, table, None)
      )

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
        case "==" => TPTPEquality(true, translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case "!=" => TPTPEquality(false, translateExpression(l, gc, table, None), translateExpression(r, gc, table, None))
        case _    =>
          val operator = table.get(op.symbol).collect { case c: TPTPConstant => c }.getOrElse(TPTPConstant(op.symbol))
          TPTPApply(TPTPApply(operator, translateExpression(l, gc, table, None)), translateExpression(r, gc, table, None))
      }

    case Application(BaseOperator(op, _), List(x)) =>
      op.symbol match {
        case "!" => TPTPNegation(translateExpression(x, gc, table, None))
        case "-" => TPTPApply(TPTPInterpretedConstant("$uminus"), translateExpression(x, gc, table, None))
        case _   =>
          val operator = table.get(op.symbol).collect { case c: TPTPConstant => c }.getOrElse(TPTPConstant(op.symbol))
          TPTPApply(operator, translateExpression(x, gc, table, None))
      }

    case Application(tuple, List(IntValue(index)))
        if inferExprType(tuple, gc, table, None).exists(_.isInstanceOf[TPTPProductType]) =>
      TPTPApply(TPTPInterpretedConstant(s"$$proj$index"), translateExpression(tuple, gc, table, None)) //Error

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
      val inferredVars = inferFreeVariableTypes(body, gc, table)
      val declarations = Option(vars) match {
        case Some(context) => context.variables.map { v =>
          val tp = Option(v.tp) match {
            case Some(t) if t != null && !t.isInstanceOf[UnknownType] => translateType(t, gc, table)
            case _ => inferredVars.getOrElse(v.name, TPTPInterpretedConstant("$i"))
          }
          (v.name, tp)
        }
        case None => freeVariableNames(body, knownSymbols = table.keySet.toSet).toList.sorted.map { name =>
          (name, inferredVars.getOrElse(name, TPTPInterpretedConstant("$i")))
        }
      }
      val newTable = HashMap(table.toSeq: _*)
      declarations.foreach { case (name, tp) =>
        newTable(name) = tp
        newTable(variableMarker(name)) = TPTPVariable(name)
      }
      if (declarations.isEmpty) translateExpression(body, gc, newTable, None)
      else {
        val ctx = TPTPContext(declarations.map { case (name, tp) => (name.capitalize, tp) })
        TPTPQuantifier(univ, ctx, translateExpression(body, gc, newTable, None))
      }

    case OwnedExpr(owner, _, inner) =>
      ownedAccessInfo(owner, inner, table) match {
        case Some((qualifiedName, _)) => TPTPConstant(qualifiedName)
        case None => translateExpression(inner, gc, table, expectedTp)
      }

    case Instance(theory) =>
      TPTPConstant("instance_value")

    case Lambda(ins, body, _) =>
      var curTp = expectedTp
      val newTable = HashMap(table.toSeq: _*)
      val ctxDecls = ins.variables.reverse.map { v =>
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
              case _ => TPTPInterpretedConstant("$int")
            }
        }
        curTp = curTp match {
          case Some(TPTPFunType(_, rng)) => Some(rng)
          case _ => None
        }
        newTable(v.name) = vTp
        newTable(variableMarker(v.name)) = TPTPVariable(v.name)
        (v.name.capitalize, vTp)
      }
      val ctx = TPTPContext(ctxDecls)
      TPTPLambda(ctx, translateExpression(body, gc, newTable, curTp))
  }

  private def containsInstance(expr: Expression): Boolean = expr match {
    case _: Instance => true
    case Application(fun, args) => containsInstance(fun) || args.exists(containsInstance)
    case OwnedExpr(owner, _, inner) => containsInstance(owner) || containsInstance(inner)
    case Equality(_, _, left, right) => containsInstance(left) || containsInstance(right)
    case Assert(test, _, expected) => containsInstance(test) || containsInstance(expected)
    case Quantifier(_, vars, body) => Option(vars).exists(_.variables.exists(v => v.dfO.exists(containsInstance))) || containsInstance(body)
    case Lambda(ins, body, _) => ins.variables.exists(v => v.dfO.exists(containsInstance)) || containsInstance(body)
    case IfThenElse(cond, thn, els) => containsInstance(cond) || containsInstance(thn) || els.exists(containsInstance)
    case Tuple(es) => es.exists(containsInstance)
    case Projection(tuple, _) => containsInstance(tuple)
    case AppliedRef(ref, _, args) => containsInstance(ref) || args.exists(containsInstance)
    case ListElem(list, pos) => containsInstance(list) || containsInstance(pos)
    case Block(exprs) => exprs.exists(containsInstance)
    case Assign(target, value) => containsInstance(target) || containsInstance(value)
    case Return(exp, _) => containsInstance(exp)
    case _ => false
  }

  private def safeNamePart(name: String): String = {
    val cleaned = name.map(c => if (c.isLetterOrDigit || c == '_') c else '_')
    if (cleaned.isEmpty) "field"
    else if (cleaned.head.isLetter && cleaned.head.isUpper) cleaned.head.toLower + cleaned.tail
    else if (cleaned.head.isLetter || cleaned.head == '_') cleaned
    else "f_" + cleaned
  }

  private def containsUndefined(expr: Expression): Boolean = expr match {
    case _: UndefinedValue => true
    case Application(fun, args) => containsUndefined(fun) || args.exists(containsUndefined)
    case OwnedExpr(owner, _, inner) => containsUndefined(owner) || containsUndefined(inner)
    case Equality(_, _, left, right) => containsUndefined(left) || containsUndefined(right)
    case Assert(test, _, expected) => containsUndefined(test) || containsUndefined(expected)
    case Quantifier(_, vars, body) => Option(vars).exists(_.variables.exists(v => v.dfO.exists(containsUndefined))) || containsUndefined(body)
    case Lambda(ins, body, _) => ins.variables.exists(v => v.dfO.exists(containsUndefined)) || containsUndefined(body)
    case IfThenElse(cond, thn, els) => containsUndefined(cond) || containsUndefined(thn) || els.exists(containsUndefined)
    case Tuple(es) => es.exists(containsUndefined)
    case Projection(tuple, _) => containsUndefined(tuple)
    case AppliedRef(ref, _, args) => containsUndefined(ref) || args.exists(containsUndefined)
    case ListElem(list, pos) => containsUndefined(list) || containsUndefined(pos)
    case Block(exprs) => exprs.exists(containsUndefined)
    case Assign(target, value) => containsUndefined(target) || containsUndefined(value)
    case Return(exp, _) => containsUndefined(exp)
    case _ => false
  }

  private def translateInstanceFields(ownerName: String, instance: Instance, gc: GlobalContext, table: HashMap[String, TPTPFormula]): List[TPTPDecl] = {
    val localTable = HashMap(table.toSeq: _*)
    instance.theory.decls.collect { case td: TypeDecl if td.dfO.isDefined => td }.foreach { td =>
      val aliasedType = translateType(td.dfO.get, gc, localTable, None)
      localTable(td.name) = aliasedType
      localTable(typeAliasMarker(td.name)) = aliasedType
    }

    val fields = instance.theory.decls.collect { case ed: ExprDecl => ed }
    val fieldTypes = fields.map { field =>
      val qualifiedName = s"owned_${safeNamePart(ownerName)}_${safeNamePart(field.name)}"
      val explicitType = Option(field.tp).filter(tp => tp != null && tp != AnyType && !tp.isInstanceOf[UnknownType])
        .map(tp => translateType(tp, gc, localTable, field.dfO))
      val inferredType = field.dfO.filterNot(containsInstance).filterNot(containsUndefined)
        .flatMap(expr => inferExprType(expr, gc, localTable, None))
      val fieldType = explicitType.orElse(inferredType).orElse(table.get(field.name)).getOrElse(TPTPInterpretedConstant("$i"))
      localTable(qualifiedName) = fieldType
      localTable(field.name) = fieldType
      localTable(symbolMarker(field.name)) = TPTPConstant(qualifiedName)
      field.ntO.foreach { case Notation(_, symbol) => localTable(symbol) = TPTPConstant(qualifiedName) }
      (field, qualifiedName, fieldType)
    }

    val typeDecls = fieldTypes.map { case (_, qualifiedName, fieldType) =>
      TPTPDecl(s"${qualifiedName}_type", "type", TPTPTypeAssignment(TPTPConstant(qualifiedName), fieldType))
    }
    val definitions = fieldTypes.flatMap { case (field, qualifiedName, fieldType) =>
      val valueDef = field.dfO.filterNot(containsInstance).filterNot(containsUndefined).map { expr =>
        val ownedDecls = declareOwnedReferences(expr, localTable)
        ownedDecls :+ TPTPDecl(s"${qualifiedName}_def", "axiom",
          TPTPEquality(true, TPTPConstant(qualifiedName), translateExpression(expr, gc, localTable, Some(fieldType))))
      }.getOrElse(Nil)
      val nestedInstances = field.dfO.collect { case nested: Instance => translateInstanceFields(qualifiedName.stripPrefix("owned_"), nested, gc, localTable) }.getOrElse(Nil)
      valueDef ++ nestedInstances
    }

    typeDecls ++ definitions
  }

  private def expressionName(expr: Expression): Option[String] = expr match {
    case ClosedRef(name) => Some(name)
    case OpenRef(path) => Some(path.names.mkString("_"))
    case OwnedExpr(owner, _, inner) => ownedAccessInfo(owner, inner).map(_._1)
    case AppliedRef(ref, _, args) if args.isEmpty => expressionName(ref)
    case _ => None
  }

  private def ownedAccessInfo(owner: Expression, inner: Expression): Option[(String, String)] =
    ownedAccessInfo(owner, inner, HashMap[String, TPTPFormula]())

  private def ownedAccessInfo(owner: Expression, inner: Expression, table: HashMap[String, TPTPFormula]): Option[(String, String)] = {
    for {
      ownerName <- expressionName(owner)
      fieldName <- expressionName(inner)
    } yield {
      val aliasedOwner = table.get(symbolMarker(ownerName)).collect {
        case TPTPConstant(name) if name.startsWith("owned_") => name
      }
      val qualifiedName = aliasedOwner match {
        case Some(name) => s"${name}_${safeNamePart(fieldName)}"
        case None if ownerName.startsWith("owned_") => s"${ownerName}_${safeNamePart(fieldName)}"
        case None => s"owned_${safeNamePart(ownerName)}_${safeNamePart(fieldName)}"
      }
      (qualifiedName, fieldName)
    }
  }

  private def declaredFieldType(fieldName: String, table: HashMap[String, TPTPFormula], modules: Map[String, Module]): Option[TPTPFormula] = {
    val fromModules = modules.values.toList.flatMap { module =>
      module.decls.collect {
        case field: ExprDecl
            if field.name == fieldName && field.tp != null && field.tp != AnyType &&
              !field.tp.isInstanceOf[UnknownType] && !field.tp.isInstanceOf[ProofType] =>
          translateType(field.tp, null, table, field.dfO)
      }
    }.headOption

    fromModules.orElse(table.get(fieldName))
  }

  private def declareOwnedReferences(expr: Expression, table: HashMap[String, TPTPFormula], modules: Map[String, Module] = Map.empty): List[TPTPDecl] = {
    def accesses(e: Expression): List[(String, String)] = e match {
      case OwnedExpr(owner, _, inner) =>
        ownedAccessInfo(owner, inner, table).toList ::: accesses(owner) ::: accesses(inner)
      case Application(fun, args) => accesses(fun) ::: args.flatMap(accesses)
      case Equality(_, _, left, right) => accesses(left) ::: accesses(right)
      case Assert(test, _, expected) => accesses(test) ::: accesses(expected)
      case Quantifier(_, _, body) => accesses(body)
      case Lambda(_, body, _) => accesses(body)
      case IfThenElse(cond, thn, els) => accesses(cond) ::: accesses(thn) ::: els.toList.flatMap(accesses)
      case Tuple(es) => es.flatMap(accesses)
      case Projection(tuple, _) => accesses(tuple)
      case AppliedRef(ref, _, args) => accesses(ref) ::: args.flatMap(accesses)
      case ListElem(list, pos) => accesses(list) ::: accesses(pos)
      case Block(exprs) => exprs.flatMap(accesses)
      case Assign(target, value) => accesses(target) ::: accesses(value)
      case Return(exp, _) => accesses(exp)
      case _ => Nil
    }

    accesses(expr).distinct.map { case (qualifiedName, fieldName) =>
      val fieldType = table.get(qualifiedName)
        .orElse(declaredFieldType(fieldName, table, modules))
        .getOrElse(TPTPInterpretedConstant("$i"))
      table(qualifiedName) = fieldType
      TPTPDecl(s"${qualifiedName}_type", "type", TPTPTypeAssignment(TPTPConstant(qualifiedName), fieldType))
    }
  }

  private def freeVariableNames(expr: Expression, bound: Set[String] = Set.empty, knownSymbols: Set[String] = Set.empty): Set[String] = expr match {
    case VarRef(name) => if (bound(name)) Set.empty else Set(name)
    case ClosedRef(name) if name.nonEmpty && name.head.isLower && !bound(name) && !knownSymbols(name) => Set(name)
    case Application(fun, args) => freeVariableNames(fun, bound, knownSymbols) ++ args.flatMap(freeVariableNames(_, bound, knownSymbols))
    case OwnedExpr(owner, _, inner) => freeVariableNames(owner, bound, knownSymbols) ++ freeVariableNames(inner, bound, knownSymbols)
    case Equality(_, _, left, right) => freeVariableNames(left, bound, knownSymbols) ++ freeVariableNames(right, bound, knownSymbols)
    case Assert(test, _, expected) => freeVariableNames(test, bound, knownSymbols) ++ freeVariableNames(expected, bound, knownSymbols)
    case Quantifier(_, null, _) => Set.empty 
    case Quantifier(_, vars, body) => freeVariableNames(body, bound ++ vars.variables.map(_.name), knownSymbols)
    case Lambda(ins, body, _) => freeVariableNames(body, bound ++ ins.variables.map(_.name), knownSymbols)
    case IfThenElse(cond, thn, els) => freeVariableNames(cond, bound, knownSymbols) ++ freeVariableNames(thn, bound, knownSymbols) ++ els.toList.flatMap(freeVariableNames(_, bound, knownSymbols))
    case Tuple(es) => es.flatMap(freeVariableNames(_, bound, knownSymbols)).toSet
    case Projection(tuple, _) => freeVariableNames(tuple, bound, knownSymbols)
    case AppliedRef(ref, _, args) => freeVariableNames(ref, bound, knownSymbols) ++ args.flatMap(freeVariableNames(_, bound, knownSymbols))
    case ListElem(list, pos) => freeVariableNames(list, bound, knownSymbols) ++ freeVariableNames(pos, bound, knownSymbols)
    case _ => Set.empty
  }

  private def inferFreeVariableTypes(expr: Expression, gc: GlobalContext, table: HashMap[String, TPTPFormula]): Map[String, TPTPFormula] = {
    val inferred = HashMap[String, TPTPFormula]()

    def constrain(e: Expression, expected: TPTPFormula): Unit = e match {
      case VarRef(name) => inferred.getOrElseUpdate(name, expected)
      case ClosedRef(name) if name.nonEmpty && name.head.isLower && !table.contains(name) => inferred.getOrElseUpdate(name, expected)
      case OwnedExpr(_, _, inner) => constrain(inner, expected)
      case Equality(_, _, left, right) => constrain(left, expected); constrain(right, expected)
      case _ => ()
    }

    def visit(e: Expression): Unit = e match {
      case Application(fun, args) =>
        var current = inferExprType(fun, gc, table, None)
        args.foreach { arg =>
          current match {
            case Some(TPTPFunType(domain, range)) => constrain(arg, domain); current = Some(range)
            case _ => current = None
          }
          visit(arg)
        }
        visit(fun)
      case Equality(_, _, left, right) =>
        val tp = inferExprType(left, gc, table, None).orElse(inferExprType(right, gc, table, None))
        tp.foreach { t => constrain(left, t); constrain(right, t) }
        visit(left); visit(right)
      case Assert(test, _, expected) => visit(test); visit(expected)
      case OwnedExpr(owner, _, inner) => visit(owner); visit(inner)
      case Quantifier(_, _, body) => visit(body)
      case Lambda(_, body, _) => visit(body)
      case IfThenElse(cond, thn, els) => visit(cond); visit(thn); els.foreach(visit)
      case Tuple(es) => es.foreach(visit)
      case Projection(tuple, _) => visit(tuple)
      case AppliedRef(ref, _, args) => visit(ref); args.foreach(visit)
      case ListElem(list, pos) => visit(list); visit(pos)
      case _ => ()
    }

    visit(expr)
    inferred.toMap
  }

  def translateDecl(decl: Declaration, gc: GlobalContext, table: HashMap[String, TPTPFormula]): List[TPTPDecl] = decl match {
    case module: Module =>
      table(module.name) = TPTPInterpretedConstant("$i")
      module.decls.flatMap(d => translateDecl(d, gc, table))

    case theory: Theory =>
      theory.decls.flatMap(d => translateDecl(d, gc, table))


    case _: Include =>
      Nil

    case ed: ExprDecl if ed.tp.isInstanceOf[ProofType] && ed.dfO.exists(_.isInstanceOf[UndefinedValue]) =>
      val formula = ed.tp.asInstanceOf[ProofType].formula
      val ownedDecls = declareOwnedReferences(formula, table)
      ownedDecls :+ TPTPDecl(
        ed.name,
        "conjecture",
        translateExpression(formula, gc, table, None)
    )
    
    case ed: ExprDecl if ed.tp.isInstanceOf[ProofType] && ed.dfO.isEmpty =>
      table(ed.name) = TPTPInterpretedConstant("$o")
      val formula = ed.tp.asInstanceOf[ProofType].formula
      val ownedDecls = declareOwnedReferences(formula, table)
      ownedDecls :+ TPTPDecl(ed.name, "axiom", translateExpression(formula, gc, table, None))

    case ed: ExprDecl => 
      val expectedTy: Option[TPTPFormula] = Option(ed.tp) match {
        case Some(tp) if tp != null && tp != AnyType && !tp.isInstanceOf[UnknownType] => 
          Some(translateType(tp, gc, table, ed.dfO))
        case _ => 
          ed.dfO.flatMap(expr => inferExprType(expr, gc, table, None))
      }

      val inferredTp = ed.dfO.flatMap(expr => inferExprType(expr, gc, table, expectedTy))

      val resolvedType: TPTPFormula = expectedTy match {
        case Some(tp) if tp != null && (!containsI(tp) || isStructureValueType(ed.tp, table)) => tp
        case _ => inferredTp.getOrElse(TPTPInterpretedConstant("$int"))
      }

      table(ed.name) = resolvedType
      ed.ntO.foreach {
        case Notation(_, symbol) => table(symbol) = TPTPConstant(ed.name)
      }
      val ownedDecls = ed.dfO.filterNot(containsInstance).toList.flatMap(expr => declareOwnedReferences(expr, table))

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
      val axiomDecl = ed.dfO.filterNot(containsInstance).filterNot(containsUndefined).map { expr =>
        TPTPDecl(s"${ed.name}_def", "axiom", TPTPEquality(true, TPTPConstant(ed.name), translateExpression(expr, gc, table, expectedTy)))
      }
      val instanceFields = ed.dfO.collect { case instance: Instance => translateInstanceFields(ed.name, instance, gc, table) }.getOrElse(Nil)

      List(typeDecl) ++ ownedDecls ++ instanceFields ++ axiomDecl.toList
  
    case td: TypeDecl => 
      td.dfO match {
        case Some(targetType) =>
          val aliasedType = translateType(targetType, gc, table, None)
          table(td.name) = aliasedType
          table(typeAliasMarker(td.name)) = aliasedType
          Nil

        case None =>
          table(typeAliasMarker(td.name)) = TPTPConstant(td.name)
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
    case BaseOperator(_, tp) if tp != null && !tp.isInstanceOf[UnknownType] => Some(translateType(tp, gc, table, None))
    case BaseOperator(op, _) => table.get(op.symbol).collect { case TPTPConstant(name) => table.get(name) }.flatten
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

    case OwnedExpr(owner, _, inner) =>
      ownedAccessInfo(owner, inner, table).flatMap { case (qualifiedName, fieldName) =>
        table.get(qualifiedName).orElse(table.get(fieldName))
      }.orElse(inferExprType(inner, gc, table, expectedTp))

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
    case _: ProofType => TPTPInterpretedConstant("$o")
    case ClassType(_) => TPTPInterpretedConstant("$i")
    case OwnedType(_, _, inner) => translateType(inner, gc, table, bodyContext)
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
      val withTpArgs = tpargs.foldLeft(base) { (fun, arg) =>
        TPTPApply(fun, translateType(arg, gc, table, bodyContext))
      }
      args.foldLeft(withTpArgs) { (fun, arg) =>
        TPTPApply(fun, translateExpression(arg, gc, table, None))
      }
    case OpenRef(path) =>
      table.get(path.names.mkString("_"))
        .orElse(path.names.lastOption.flatMap(name => table.get(typeAliasMarker(name))))
        .getOrElse(TPTPConstant(path.names.mkString("_")))
    case _: UnknownType =>
      bodyContext match {
        case Some(body) if containsArithmetic(body) => TPTPInterpretedConstant("$int")
        case _ => TPTPInterpretedConstant("$int")
      }
    case _ =>
      bodyContext match {
        case Some(body) if containsArithmetic(body) => TPTPInterpretedConstant("$int")
        case _ => TPTPInterpretedConstant("$int")
      }
  }
}
