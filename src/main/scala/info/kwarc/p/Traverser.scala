package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods
  *
  * All methods carry a state a:A.
  * All local variable bindings pass through applyVarDecl, which also returns an updated state for use in the variable's scope.
  *
  * The value 'null' is respected for theories and contexts, assuming they are inferred later.
  *
  * You can also use an Extractor-pattern to apply the Traverser, and continue matching on the result.
  */
abstract class Traverser[A] {
  @inline def apply(p: Path)(implicit gc: GlobalContext, a: A): Path = matchC(p) {p => p}
  @inline def apply(r: Ref)(implicit gc: GlobalContext, a: A): Ref = r match {
    case OpenRef(p) => OpenRef(apply(p)).copyFrom(r)
    case _ => r
  }

  def apply(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = matchC(d)(applyDefault _)
  protected final def applyDefault(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = d match {
    case m@Module(n,op,df) =>
      val gcI = gc.enter(m)
      val dsT = df.decls.map(d => apply(d)(gcI, a))
      Module(n, op, TheoryValue(dsT))
    case Include(dm,df, r) =>
      Include(apply(dm), df map apply, r)
    case TypeDecl(n, tc, bd, dfO, ms) =>
      val (tcT,aT) = apply(tc)
      TypeDecl(n, tcT, apply(bd)(gc,aT), dfO map {d => apply(d)(gc,aT)}, ms)
    case ExprDecl(n, tc, tp, dfO, ntO, ms) =>
      val (tcT,aT) = apply(tc)
      ExprDecl(n, tcT, apply(tp)(gc,aT), dfO map {d => apply(d)(gc,aT)}, ntO, ms)
  }

  /** must satisfy apply(thy.toValue) == apply(thy).toValue */
  def apply(thy: Theory)(implicit gc: GlobalContext, a: A): Theory = matchC(thy)(applyDefault _)
  protected final def applyDefault(thy: Theory)(implicit gc: GlobalContext, a: A) = thy match {
    case null => null
    case r: Ref => apply(r)
    case OwnedTheory(o,d,t) =>
      val tT = apply(t)(gc.push(d,Some(o)), a)
      OwnedTheory(apply(o), apply(d), tT)
    case TheoryValue(ds) =>
      val gcI = gc.enter(thy)
      val dsT = ds map {d => apply(d)(gcI,a)}
      TheoryValue(dsT)
  }

  def apply(ctx: LocalContext)(implicit gc: GlobalContext, a:A): (LocalContext,A) = {
    if (ctx == null) (null,a) else {
      var aT = a
      var gcI = gc
      val ctxT = matchC(ctx) {ctx =>
        ctx.map {d =>
          val (vdT,_a) = applyVarDecl(d)(gcI,aT)
          gcI = gcI.append(vdT)
          aT = _a
          vdT
        }
      }
      (ctxT.copyFrom(ctx), aT)
    }
  }

  def apply(ctx: ExprContext)(implicit gc: GlobalContext, a:A): (ExprContext,A) = {
    if (ctx == null) (null,a) else {
      val (ctxT, aT) = apply(ctx.toLocalContext)
      (ExprContext.force(ctxT), aT)
    }
  }

  def applyVarDecl(vd: VarDecl)(implicit gc: GlobalContext, a:A): (VarDecl,A) = {
    val vdT = matchC(vd) {
      case EVarDecl(n,t,d,m,o) => EVarDecl(n, if (t == null) null else apply(t), d map apply, m, o)
      case TVarDecl(n,d) => TVarDecl(n, d map apply)
    }
    (vdT,a)
  }
  def applyEVarDecl(vd: EVarDecl)(implicit gc: GlobalContext, a:A): (EVarDecl,A) = {
    val (vdT,aT) = applyVarDecl(vd)
    (vdT.asInstanceOf[EVarDecl], aT)
  }

  def apply(rc: RegionalContext)(implicit gc: GlobalContext, a:A): RegionalContext = {
    RegionalContext(apply(rc.theory).toValue, rc.owner map apply, apply(rc.local)._1).copyFrom(rc)
  }

  def apply(sub: Substitution)(implicit gc: GlobalContext, a: A) = sub.map {vd => applyVarDecl(vd)._1}

  // occasionally these substitutions must be treated differently, so this can be overridden here
  def applySubstitutionInUnknown(u: UnknownObject, sub: Substitution)(implicit gc: GlobalContext, a: A) = apply(sub)

  def apply(tp: Type)(implicit gc: GlobalContext, a: A): Type = matchC(tp)(applyDefault _)
  protected final def applyDefault(tp: Type)(implicit gc: GlobalContext, a: A): Type = tp match {
    case u @ UnknownType(g,cont,sub) =>
      if (cont.known) apply(tp.skipUnknown)  // eliminate unknown-wrappers
      else UnknownType(g,cont, if (sub == null) null else applySubstitutionInUnknown(u,sub))
    case r: Ref => apply(r)
    case AppliedRef(r, tps, es) => AppliedRef(apply(r), tps map apply, es map apply)
    case OwnedType(e, d, o) => OwnedType(apply(e), apply(d), apply(o)(gc.push(d,Some(e)),a))
    case b: BaseType => b
    case ExceptionType => tp
    case IntervalType(l,u) => IntervalType(l map apply, u map apply)
    case ClassType(thy) => ClassType(apply(thy))
    case ExprsOver(thy,q) => ExprsOver(apply(thy), apply(q)(gc.pushQuoted(thy),a))
    case FunType(ins,t) =>
      val (insT,aT) = apply(ins)
      FunType(insT, apply(t)(gc.append(ins), aT))
    case ProdType(ts) => ProdType(apply(ts)._1)
    case CollectionType(b,k) => CollectionType(apply(b), k)
    case ProofType(f) => ProofType(apply(f))
  }

  def apply(exp: Expression)(implicit gc: GlobalContext, a: A): Expression = matchC(exp)(applyDefault _)
  protected final def applyDefault(exp: Expression)(implicit gc: GlobalContext, a: A): Expression = exp match {
    case null => null
    case u @ UnknownExpr(g,cont,tp,sub) =>
      if (cont.known) apply(exp.skipUnknown)  // eliminate unknown-wrappers
      else UnknownExpr(g, cont, tp, if (sub == null) null else applySubstitutionInUnknown(u,sub))
      // TODO not traversing into tp because it lives in context g
    case _: BaseValue => exp
    case This(l) => exp
    case r: Ref => apply(r)
    case AppliedRef(r, tps, es) => AppliedRef(apply(r), tps map apply, es map apply)
    case OwnedExpr(o, d, e) => OwnedExpr(apply(o), apply(d), apply(e)(gc.push(d,Some(o)),a))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy) => Instance(apply(thy))
    case vd:EVarDecl => applyVarDecl(vd)._1.asInstanceOf[EVarDecl]
    case Assign(k,v) => Assign(apply(k), apply(v))
    case ExprOver(t,e) => ExprOver(apply(t), apply(e)(gc.pushQuoted(t),a))
    case Eval(e) => Eval(apply(e)(gc.pop(),a))
    case Block(es) =>
      var gcI = gc
      var aI = a
      val esT = es.map {e =>
        val eT = e match {
          case vd: EVarDecl =>
            val (vdT,_a) = applyEVarDecl(vd)(gcI,aI)
            gcI = gcI.append(vd)
            aI = _a
            vdT
          case e => apply(e)(gcI,aI)
        }
        eT
      }
      Block(esT)
    case IfThenElse(c, t, e) => IfThenElse(apply(c), apply(t), e map apply)
    case Match(e, cs, h) =>
      Match(apply(e), cs map {c => apply(c).asInstanceOf[MatchCase]}, h)
    case MatchCase(ctx,p,b) =>
      val gcI = if (ctx == null) gc else gc.append(ctx)
      val (ctxT,aT) = apply(ctx)
      MatchCase(ctxT, apply(p)(gcI,aT), apply(b)(gcI,aT))
    case While(c,b) => While(apply(c), apply(b))
    case For(v,r,b) =>
      val (vT,aT) = applyEVarDecl(v)
      For(vT, apply(r), apply(b)(gc.append(v),aT))
    case Return(e, thrw) => Return(apply(e), thrw)
    case Lambda(is,b,mr) =>
      val (isT,aT) = apply(is)
      Lambda(isT, apply(b)(gc.append(is),aT), mr)
    case Application(f,as) => Application(apply(f), as map apply)
    case Tuple(es) => Tuple(es map apply)
    case Projection(e,i) => Projection(apply(e), i)
    case CollectionValue(es,k) => CollectionValue(es map apply,k)
    case ListElem(l,p) => ListElem(apply(l), apply(p))
    case Equality(p,t,l,r) => Equality(p, apply(t), apply(l), apply(r))
    case Quantifier(q,vs,b) =>
      val (vsT,aT) = apply(vs)
      // if the quantifiers is closing and the context has not been inferred yet, this does not pass down the correct context
      Quantifier(q, vsT, apply(b)(gc.append(vs),aT))
    case Assert(t,tp,e) => Assert(apply(t), apply(tp), apply(e))
    case Cast(e,tp) => Cast(apply(e), apply(tp))
    case UndefinedValue(tp) => UndefinedValue(apply(tp))
  }
}

abstract class StatelessTraverser extends Traverser[Unit] {
  def apply(gc: GlobalContext, d: Declaration): Declaration = apply(d)(gc,())
  def apply(gc: GlobalContext, exp: Expression): Expression = apply(exp)(gc,())
  def apply(gc: GlobalContext, tp: Type): Type = apply(tp)(gc,())
  def apply(gc: GlobalContext, thy: Theory): Theory = apply(thy)(gc,())

  /** delegates to one of the above
    * needs a separate name because of type overlaps
    * must only be called if the joint parts of Object-subclasses are treated identically
    */
  def applyObj(gc: GlobalContext, o: Object): Object = o match {
    case o: Expression => apply(o)(gc,())
    case o: Type => apply(o)(gc,())
    case o: Theory => apply(o)(gc,())
  }
}

trait TraverseOnlyOriginalRegion {
  val initGC: GlobalContext
  def inOriginalRegion(implicit gc: GlobalContext) = gc.regions.length == initGC.regions.length
  /** the variables that have been traversed during the current call */
  def localBindings(implicit gc: GlobalContext) = gc.unappend(initGC)
  def isLocallyBound(n: String)(implicit gc: GlobalContext) = localBindings.exists(_.declares(n))
}

object IdentityTraverser extends StatelessTraverser

class EvalTraverser(initGC: GlobalContext, cont: Expression => Expression) extends StatelessTraverser {
  override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = matchC(exp) {
    case Eval(e) if gc.regions.length == initGC.regions.length+1 => Eval(cont(e))
    case _ => applyDefault(exp)
  }
}
object EvalTraverser {
  def apply(e: ExprOver)(cont: Expression => Expression) = {
    val gc = GlobalContext("")
    new EvalTraverser(gc,cont).apply(e.expr)(gc, ())
  }
  /** returns the quoted expression with all evals replaced by variables and context declaring the latter */
  def replaceEvals(eo: ExprOver) = {
    var evals : List[EVarDecl] = Nil
    var i = 0
    val eoT = EvalTraverser(eo) {ev =>
      val n = ReplaceVarName(i)
      i += 1
      evals = EVarDecl(n, null, Some(ev)) :: evals
      VarRef(n)
    }
    (ExprContext.make(evals), eoT)
  }
  object ReplaceVarName extends EVarDecl.SpecialVarName("eval")
}

/** Substitution for the [This]-operator
  *
  * E << n,s arises by replacing This(l) as follows:
  * - 1   <= l <= s     unchanged
  * - s   <  l <= s+n   owner of l-th region
  * - otherwise         This(l-n)
  * s is incremented when traversing into nested regions so that they remain unchanged.
  * n is fixed during traversal.
  *
  * Then
  * if gc |- E, then gc |- E << 0,0
 *    Identity
  * if gc.push(on)....push(o1) |- E, then gc |- E << n,0
  *   Intuitively, all This(0), ..., This(n-1) are substituted by the respective owner.
  *   This takes E from a lower region and substitutes all owners.
  * if gc |- E, then gc.push(_)....push(_) |- E << -n,0
  *   Intuitively, all This(l) in E are replaced with This(l+|n|).
  *   This is needed when moving an object from a higher region into the current region.
  *
  * Below n=numSubs. s is not carried but computed by comparing the size of initial and current context.
  * If the substitution is shallow, an OwnedXXX is returned.
  * Original input is well-formed over initGC, output over initGC.pop^n.
  * Intermediate values over initGC.push...
  */
class OwnersSubstitutor(val initGC: GlobalContext, numSubs: Int) extends StatelessTraverser {

  private def owner(implicit gc: GlobalContext) = {
    val s = gc.regions.length - initGC.regions.length
    if (s > 0) None
    else {
      val reg = gc.currentRegion
      val o = reg.owner.getOrElse {
        if (numSubs<0) This(-numSubs)
        else throw IError("no owner")
      }
      Some((o,reg.theory))
    }
  }

  override def apply(thy: Theory)(implicit gc: GlobalContext, a:Unit) = matchC(thy) {
    case c: ClosedRef =>
      owner match {
        case None => c
        case Some((o,d)) => OwnedTheory(o,d,c)
      }
    case _ => applyDefault(thy)
  }
  override def apply(tp: Type)(implicit gc: GlobalContext, a:Unit) = matchC(tp) {
    case c: ClosedRef =>
      owner match {
        case None => c
        case Some((o,d)) => OwnedType(o,d,c)
      }
    case _ => applyDefault(tp)
  }
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit) = matchC(exp) {
    case c: ClosedRef =>
      owner match {
        case None => c
        case Some((o,d)) => OwnedExpr(o,d,c)
      }
    case This(l) =>
      val s = gc.regions.length - initGC.regions.length
      if (l <= s) exp
      else if (l <= s+numSubs) {
        val reg = gc.regions(l-1).region
        val o = reg.owner.getOrElse {throw IError("no owner")}
        o // TODO substitute higher owner occurring in o
      } else
        This(l-numSubs)
    case _ => applyDefault(exp)
  }
}

object OwnersSubstitutor {
  def applyDecl(gc: GlobalContext, d: Declaration, numSubs: Int = 1): Declaration = {
    if (numSubs == 0) return d
    val os = new OwnersSubstitutor(gc,numSubs)
    os.apply(d)(gc, ())
  }
  def applyTheory(gc: GlobalContext, thy: Theory, numSubs: Int = 1): Theory = {
    if (numSubs == 0) return thy
    val os = new OwnersSubstitutor(gc,numSubs)
    os.apply(thy)(gc, ())
  }
  def applyType(gc: GlobalContext, tp: Type, numSubs: Int = 1): Type = {
    if (numSubs == 0) return tp
    val os = new OwnersSubstitutor(gc,numSubs)
    os.apply(tp)(gc, ())
  }
  def applyExpr(gc: GlobalContext, e: Expression, numSubs: Int = 1): Expression = {
    if (numSubs == 0) return e
    val os = new OwnersSubstitutor(gc,numSubs)
    os.apply(e)(gc, ())
  }
}

// TODO do not traverse into domain of owned objects (very slow)
class Substituter(val initGC: GlobalContext) extends Traverser[Substitution] with TraverseOnlyOriginalRegion {
  override def apply(exp: Expression)(implicit gc: GlobalContext, sub: Substitution) = matchC(exp) {
    case e if e.closing => e // no free variables in e even if they have not been inferred yet
    case VarRef(n) if n != "" && inOriginalRegion => sub.lookupO(n) match {
      case Some(vd: EVarDecl) => vd.dfO.get
      case Some(_) => throw IError("unexpected substitute")
      case None => exp
    }
    case _ => applyDefault(exp)
  }
  override def apply(tp: Type)(implicit gc: GlobalContext, sub: Substitution) = matchC(tp) {
    case VarRef(n) if n != "" && inOriginalRegion => sub.lookupO(n) match {
      case Some(vd: TVarDecl) => vd.dfO.get
      case Some(_) => throw IError("unexpected substitute")
      case None => tp
    }
    case _ => applyDefault(tp)
  }
  override def applyVarDecl(vd: VarDecl)(implicit gc: GlobalContext, sub: Substitution) = {
    if (!inOriginalRegion) super.applyVarDecl(vd) else {
      val renamed = vd.name // TODO avoid capture
      val subT = sub.appendRename(vd,renamed)
      val (vdS,_) = super.applyVarDecl(vd)
      (vdS,subT)
    }
  }
}
object Substituter {
  def applyObj(gc: GlobalContext, sub: Substitution, o: Object) = {
     o match {
       case e: Expression => apply(gc,sub,e)
       case t: Type => apply(gc,sub,t)
       case t: Theory => t // TODO how to substitute in theory?
     }
  }

  def apply(gc: GlobalContext, sub: Substitution, e: Expression) = {
    if (sub.isIdentity) e else
      new Substituter(gc)(e)(gc,sub)
  }
  def apply(gc: GlobalContext, sub: Substitution, y: Type) = {
    if (sub.isIdentity) y else
      new Substituter(gc)(y)(gc,sub)
  }
}

object Simplify extends StatelessTraverser {
  // TODO This is currently applied inside [[ProofType]] as well, resulting in `|- true`, or `|- false`
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit): Expression = {
    val expR = applyDefault(exp) // first, recursively simplify subexpressions
    matchC(expR) {
      case r: Ref => gc.lookupRef(r) match {
        // TODO Do we really want to de-ref everything? (E.g. '???' doesn't seem sensible)
        case Some(ed: ExprDecl) if !ed.modifiers.mutable && ed.dfO.isDefined => apply(ed.dfO.get)
        case _ => expR
      }
      case Application(bo: BaseOperator, args) => Operator.simplify(bo, args)
      // TODO Steffi `case Application(OpenRef(upl.math)) => Math.sin(args(0))`
      // TODO Steffi Math lib func [[Application]] for Numbers => `App(OpenRef(Mathlib.sin, 1.0) => NumberValue(scala.math.sin(1.0))`
      // TODO Steffi better with object MathLib --> sin(NumberValue x) -> NumberValue(scala.math.sin(x))
      case Projection(Tuple(es),i) => es(i-1)
      case ListElem(CollectionValue(es,k),IntValue(i)) => es(i.toInt)
      case Application(Lambda(vs,b,false), as) => Substituter(gc, vs.substitute(as), b)
      case Equality(p,_:BaseType,l:BaseValue,r:BaseValue) => BoolValue(p == (l == r))
      // TODO Do we actually want to compare expressions that couldn't be simplified
      case Equality(p,_:BaseType,l,r) => BoolValue(p == (l == r))
      case Equality(p,_:ProofType,_,_) => BoolValue(p)
      case Equality(p, tp:ProdType, Tuple(ls), Tuple(rs)) =>
        val sub = tp.comps.substitute(ls)
        val tpsS = tp.declsRev.zipWithIndex.map {case (vd,i) => Substituter(gc,sub.take(i),vd.tp)}
        val lrs = (ls zip rs).zip(tpsS).map {case ((l, r), t) => Equality(p,t,l,r)}
        Equality.reduce(p)(lrs)
      case Equality(p, CollectionType(a,k), lc: CollectionValue, rc: CollectionValue) =>
        val ls = lc.copy(kind = k).normalize.elems // convert to k, e.g., to compare lists as sets
        val rs = rc.copy(kind = k).normalize.elems
        if (ls.length != rs.length) BoolValue(!p)
        else {
          val lrs = (ls zip rs).map {case (l, r) => Equality(p,a,l,r)}
          Equality.reduce(p)(lrs)
        }
      /*case Equality(p, ExprsOver(_,a), ExprOver(_, exp1), ExprOver(_, exp2)) =>
        // theories are irrelevant for well-typed expressions
        if (exp1 == exp2)
        if (BoolValue(p == (exp1 == exp2))*/
      case e => e
    }
  }
}

/**
  * @param infer only return variables that are not declared in initGC, i.e., find the unknown context of the input
  * @param alsoRegionals treat regional names like local ones, only relevant for unchecked context
  *
  */
private class FreeVariables(val initGC: GlobalContext, infer: Boolean, alsoRegionals: Boolean) extends StatelessTraverser with TraverseOnlyOriginalRegion {
  private var names: List[String] = Nil
  override def apply(r: Ref)(implicit gc: GlobalContext, a:Unit) = {
    if (inOriginalRegion) r match {
      case VarRef(n) =>
        if (!infer || !isLocallyBound(n))
          names ::= n
      case ClosedRef(n) if alsoRegionals =>
        if (!infer || gc.resolveName(r).isEmpty)
          names ::= n
      case _ =>
    }
    r
  }
}
object FreeVariables {
  /** the list of free local/regional names not bound and not declared in the context */
  def collect(gc: GlobalContext, o: Object, infer: Boolean = false, alsoRegionals: Boolean = false) = {
    val fv = new FreeVariables(gc, infer, alsoRegionals)
    fv.applyObj(gc,o)
    fv.names.distinct
  }
}

private class Regionals(val initGC: GlobalContext) extends StatelessTraverser with TraverseOnlyOriginalRegion {
  var exps: List[String] = Nil
  var types: List[String] = Nil
  var theories: List[String] = Nil
  private def doObject(o: Object)(implicit gc: GlobalContext) = o match {
    case ClosedRef(n) if inOriginalRegion => List(n)
    case _ => Nil
  }
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit) = {
    exps :::= doObject(exp)
    applyDefault(exp)
  }
  override def apply(tp: Type)(implicit gc: GlobalContext, a:Unit) = {
    types :::= doObject(tp)
    applyDefault(tp)
  }
  override def apply(thy: Theory)(implicit gc: GlobalContext, a:Unit) = {
    theories :::= doObject(thy)
    applyDefault(thy)
  }
}

object Regionals {
  /**
   * returns the regional expression/type/theory identifiers occurring in an object
   *
   * limitation: if the object is just a regional identifier, it is treated as an expression
   */
  def apply(o: Object) = {
    val gc = GlobalContext("") // operation is not context-sensitive
    val tr = new Regionals(gc)
    o match {
      case o: Expression => tr(o)(gc,())
      case o: Type => tr(o)(gc,())
      case o: Theory => tr(o)(gc,())
    }
    (Util.distinct(tr.exps), Util.distinct(tr.types), Util.distinct(tr.theories))
  }
}

/** auxiliary code to test if  */
object TestLocationFields extends StatelessTraverser {
  def test(sf: SyntaxFragment) = {
    if (sf != null && sf.loc == null)
      println(s"${sf.getClass.getSimpleName} with missing location: ${sf.toStringShort}")
  }
  override def apply(decl: Declaration)(implicit gc: GlobalContext, a: Unit) = {
    test(decl)
    applyDefault(decl)
  }
  override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = {
    test(exp)
    applyDefault(exp)
  }
  override def apply(tp: Type)(implicit gc: GlobalContext, a: Unit) = {
    tp match {
      case _: UnknownType =>
      case _ => test(tp)
    }
    applyDefault(tp)
  }
  override def apply(thy: Theory)(implicit gc: GlobalContext, a: Unit) = {
    test(thy)
    applyDefault(thy)
  }
}



