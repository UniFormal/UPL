package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods
  *
  * All methods carry a state a:A.
  * All local variable bindings pass through applyVarDecl, which also returns an updated state for use in the variable's scope.
  *
  * The value 'null' is respected for theories and contexts, assuming they are infered later.
  */
abstract class Traverser[A] {
  def apply(p: Path)(implicit gc: GlobalContext, a: A): Path = matchC(p) {p => p}
  def apply(r: Ref)(implicit gc: GlobalContext, a: A): Ref = matchC(r) {
    case VarRef(n) => VarRef(n)
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
  }

  /** must satisfy apply(thy.toValue) == apply(thy).toValue */
  def apply(thy: Theory)(implicit gc: GlobalContext, a: A): Theory = applyDefault(thy)

  protected final def applyDefault(thy: Theory)(implicit gc: GlobalContext, a: A) = matchC(thy) {
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
      (ctxT, aT)
    }
  }

  def applyVarDecl(vd: VarDecl)(implicit gc: GlobalContext, a:A): (VarDecl,A) = {
    val VarDecl(n,t,d,m,o) = vd
    (VarDecl(n, apply(t), d map apply, m, o), a)
  }

  def apply(rc: RegionalContext)(implicit gc: GlobalContext, a:A): RegionalContext = {
    RegionalContext(apply(rc.theory).toValue, rc.owner map apply, apply(rc.local)._1)
  }

  def apply(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = matchC(d)(applyDefault _)

  protected final def applyDefault(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = d match {
    case m@Module(n,op,df) =>
      val gcI = gc.enter(m)
      val dsT = df.decls.map(d => apply(d)(gcI, a))
      Module(n, op, TheoryValue(dsT))
    case Include(dm,df, r) =>
      Include(apply(dm), df map apply, r)
    case TypeDecl(n, bd, dfO, ms) =>
      TypeDecl(n, apply(bd), dfO map apply, ms)
    case ExprDecl(n, tp, dfO, ms) =>
      ExprDecl(n, apply(tp), dfO map apply, ms)
  }

  def apply(tp: Type)(implicit gc: GlobalContext, a: A): Type = matchC(tp)(applyDefault _)

  protected final def applyDefault(tp: Type)(implicit gc: GlobalContext, a: A): Type = tp match {
    case UnknownType(g,cont,sub) =>
      if (cont.known)
        applyDefault(tp.skipUnknown)  // eliminate unknown-wrappers
      else {
        val subT = if (sub != null)
          // or traverse into the substitution values (this gives the right results for collecting free variables and applying substitutions)
          sub.map {vd => vd.copy(dfO = vd.dfO map applyDefault)}
        else null
        UnknownType(g,cont, subT)
      }
    case r: Ref => apply(r)
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
    case _: BaseValue => exp
    case r: Ref => apply(r)
    case This(l) => This(l)
    case OwnedExpr(o, d, e) => OwnedExpr(apply(o), apply(d), apply(e)(gc.push(d,Some(o)),a))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy) => Instance(apply(thy))
    case vd:VarDecl => applyVarDecl(vd)._1
    case Assign(k,v) => Assign(apply(k), apply(v))
    case ExprOver(t,e) => ExprOver(apply(t), apply(e)(gc.pushQuoted(t),a))
    case Eval(e) => Eval(apply(e)(gc.pop(),a))
    case Block(es) =>
      var gcI = gc
      var aI = a
      val esT = es.map {e =>
        val eT = e match {
          case vd: VarDecl =>
            val (vdT,_a) = applyVarDecl(vd)(gcI,aI)
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
      val (vT,aT) = applyVarDecl(v)
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
      Quantifier(q, vsT, apply(b)(gc.append(vs),aT))
    case Assert(f) => Assert(apply(f))
    case UndefinedValue(tp) => UndefinedValue(apply(tp))
  }
}

abstract class StatelessTraverser extends Traverser[Unit] {
  def apply(gc: GlobalContext, d: Declaration): Declaration = apply(d)(gc,())
  def apply(gc: GlobalContext, exp: Expression): Expression = apply(exp)(gc,())
  def apply(gc: GlobalContext, tp: Type): Type = apply(tp)(gc,())
  def apply(gc: GlobalContext, thy: Theory): Theory = apply(thy)(gc,())
}

trait TraverseOnlyOriginalRegion {
  val initGC: GlobalContext
  def inOriginalRegion(implicit gc: GlobalContext) = gc.regions.length == initGC.regions.length
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
    var evals : List[VarDecl] = Nil
    var i = 0
    val eoT = EvalTraverser(eo) {ev =>
      val n = ReplaceVarName(i)
      i += 1
      evals = VarDecl(n, null, Some(ev)) :: evals
      VarRef(n)
    }
    (LocalContext(evals.reverse), eoT)
  }
  object ReplaceVarName extends VarDecl.SpecialVarName("eval")
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

class Substituter(val initGC: GlobalContext) extends Traverser[Substitution] with TraverseOnlyOriginalRegion {
  override def apply(exp: Expression)(implicit gc: GlobalContext, sub: Substitution) = matchC(exp) {
    case VarRef(n) if n != "" && inOriginalRegion => sub.lookupO(n) match {
      case None => exp
      case Some(vd) => vd.dfO.get
    }
    case _ => applyDefault(exp)
  }
  override def applyVarDecl(vd: VarDecl)(implicit gc: GlobalContext, sub: Substitution) = {
    if (!inOriginalRegion) super.applyVarDecl(vd) else {
      val renamed = vd.name // TODO avoid capture
      val subT = sub.append(vd.name,VarRef(renamed))
      val (vdS,_) = super.applyVarDecl(vd)
      (vdS,subT)
    }
  }
}
object Substituter {
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
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit): Expression = {
    val expR = applyDefault(exp) // first, recursively simplify subexpressions
    matchC(expR) {
      case r: Ref => gc.lookupRef(r) match {
        case Some(ed: ExprDecl) if !ed.modifiers.mutable && ed.dfO.isDefined => apply(ed.dfO.get)
        case _ => expR
      }
      case Application(bo: BaseOperator, args) => Operator.simplify(bo, args)
      case Projection(Tuple(es),i) => es(i-1)
      case ListElem(CollectionValue(es,k),IntValue(i)) => es(i.toInt)
      case Application(Lambda(vs,b,false), as) => Substituter(gc, vs.substitute(as), b)
      case Equality(p,_:BaseType,l,r) => BoolValue(p == (l == r))
      case Equality(p,_:ProofType,_,_) => BoolValue(p)
      case Equality(p, tp:ProdType, Tuple(ls), Tuple(rs)) =>
        val sub = tp.comps.substitute(ls)
        val tpsS = tp.decls.zipWithIndex.map {case (vd,i) => Substituter(gc,sub.take(i),vd.tp)}
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

private class FreeVariables(val initGC: GlobalContext, alsoRegionals: Boolean) extends StatelessTraverser with TraverseOnlyOriginalRegion {
  private var names: List[String] = Nil
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit) = matchC(exp) {
    case VarRef(n) if inOriginalRegion && gc.resolveName(exp).isEmpty =>
      names ::= n
      exp
    case ClosedRef(n) if inOriginalRegion && gc.resolveName(exp).isEmpty =>
      if (alsoRegionals) {names ::= n; VarRef(n)} else exp
    case _ => applyDefault(exp)
  }
}
object FreeVariables {
  /** the list of free local/regional names not bound and not declared in the context */
  def infer(gc: GlobalContext, e: Expression) = {
    val fv = new FreeVariables(gc, true)
    fv(e)(gc,())
    fv.names.distinct
  }
  /** the list of unbound local names (not bound variables) */
  def collect(y: Type) = {
    val gc = GlobalContext("") // running it with the empty context excludes exactly the bound names
    val fv = new FreeVariables(gc, false)
    fv(y)(gc,())
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