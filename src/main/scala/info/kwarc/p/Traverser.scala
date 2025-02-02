package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods
  *
  * All methods carry a state a:A.
  * All local variable bindings pass through applyVarDecl, which also returns an updated state for use in the variable's scope.
  */
abstract class Traverser[A] {
  def apply(p: Path)(implicit gc: GlobalContext, a: A): Path = matchC(p) {p => p}
  def apply(thy: Theory)(implicit gc: GlobalContext, a: A): Theory = {
    if (thy == null) null else {
      val gcI = gc.enter(thy)
      val psT = thy.decls map {d => apply(d)(gcI,a)}
      Theory(psT).copyFrom(thy)
    }
  }
  def apply(ctx: LocalContext)(implicit gc: GlobalContext, a:A): (LocalContext,A) = {
    if (ctx == null) (null,a) else {
      var aT = a
      val ctxT = matchC(ctx) {ctx =>
        ctx.map {d =>
          val (vdT,_a) = applyVarDecl(d)
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
    RegionalContext(apply(rc.theory), rc.owner map apply, apply(rc.local)._1)
  }

  def apply(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = matchC(d)(applyDefault _)

  protected final def applyDefault(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = d match {
    case m@Module(n,op,ds) => Module(n, op, ds map {d => apply(d)(gc.enter(m),a)})
    case Include(dm,df, r) => Include(apply(dm), df map apply, r)
    case TypeDecl(n, bd, dfO) => TypeDecl(n, apply(bd), dfO map apply)
    case ExprDecl(n, tp, dfO, m) => ExprDecl(n, apply(tp), dfO map apply, m)
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
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
    case OwnedType(e, d, o) => OwnedType(apply(e), apply(d), apply(o)(gc.push(d,Some(e)),a))
    case b: BaseType => b
    case ExceptionType => tp
    case IntervalType(l,u) => IntervalType(l map apply, u map apply)
    case ClassType(thy) => ClassType(apply(thy))
    case ExprsOver(thy,q) => ExprsOver(apply(thy), apply(q)(gc.push(thy),a))
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
    case _: VarRef => exp
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
    case This(l) => This(l)
    case OwnedExpr(o, d, e) => OwnedExpr(apply(o), apply(d), apply(e)(gc.push(d,Some(o)),a))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy) => Instance(apply(thy))
    case vd:VarDecl => applyVarDecl(vd)._1
    case Assign(k,v) => Assign(apply(k), apply(v))
    case ExprOver(t,e) => ExprOver(apply(t), apply(e)(gc.push(t),a))
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
    case Lambda(is,b) =>
      val (isT,aT) = apply(is)
      Lambda(isT, apply(b)(gc.append(is),aT))
    case Application(f,as) => Application(apply(f), as map apply)
    case Tuple(es) => Tuple(es map apply)
    case Projection(e,i) => Projection(apply(e), i)
    case CollectionValue(es) => CollectionValue(es map apply)
    case ListElem(l,p) => ListElem(apply(l), apply(p))
    case Quantifier(q,vs,b) =>
      val (vsT,aT) = apply(vs)
      Quantifier(q, vsT, apply(b)(gc.append(vs),aT))
    case Assert(f) => Assert(apply(f))
  }
}

abstract class StatelessTraverser extends Traverser[Unit] {
  def apply(gc: GlobalContext, d: Declaration): Declaration = apply(d)(gc,())
  def apply(gc: GlobalContext, exp: Expression): Expression = apply(exp)(gc,())
  def apply(gc: GlobalContext, tp: Type): Type = apply(tp)(gc,())
}

trait TraverseOnlyOriginalRegion {
  val initGC: GlobalContext
  def inOriginalRegion(implicit gc: GlobalContext) = gc.regions.length == initGC.regions.length
}

object IdentityTraverser extends StatelessTraverser

class EvalTraverser(cont: Expression => Expression) extends StatelessTraverser {
  override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = matchC(exp) {
    case Eval(e) => if (gc.inPhysicalTheory) cont(e) else applyDefault(exp)
    case _ => applyDefault(exp)
  }
}
object EvalTraverser {
  def apply(e: ExprOver)(cont: Expression => Expression) = {
    val gc = GlobalContext("")
    new EvalTraverser(cont).apply(e.expr)(gc, ())
  }
  /** returns the quoted expression with all evals replaced by variables and context declaring the latter */
  def replaceEvals(eo: ExprOver) = {
    var evals : List[VarDecl] = Nil
    var i = 0
    val eoT = EvalTraverser(eo) {ev =>
      val n = "EVAL__" + i.toString
      i += 1
      evals = VarDecl(n, null, Some(ev)) :: evals
      VarRef(n)
    }
    (LocalContext(evals.reverse), eoT)
  }
}

class OwnerSubstitutor(shallow: Boolean) extends StatelessTraverser {
  private def owner(implicit gc: GlobalContext) = {
    val dos = gc.regions.collect {
      case r if r.region.owner.isDefined => (r.region.theory,r.region.owner.get)
    }
    if (dos.isEmpty) None else {
      val last = dos.last
      var dom = last._1
      var sofar = last._2
      dos.init.foreach {case (d,o) =>
        sofar = OwnedExpr(sofar,dom,o)
        dom = d
      }
      Some((sofar,dom))
    }
  }

  private def makeType(tp: Type)(implicit gc: GlobalContext) = {
    owner match {
      case None => tp
      case Some((o,d)) => OwnedType(o,d,tp)
    }
  }
  private def makeExpr(e: Expression)(implicit gc: GlobalContext) = {
    owner match {
      case None => e
      case Some((o,d)) => OwnedExpr(o,d,e)
    }
  }
  override def apply(tp: Type)(implicit gc: GlobalContext, a: Unit) = if (shallow) makeType(tp) else matchC(tp) {
    case c: ClosedRef => makeType(c)
    case e: ExprsOver => makeType(e)
    case OwnedType(o,d,t) => apply(t)(gc.push(d,Some(o)), a)
    case _ => applyDefault(tp)
  }
  override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = if (shallow) makeExpr(exp) else matchC(exp) {
    case c: ClosedRef => makeExpr(c)
    case e: ExprOver => EvalTraverser(e) {ev => apply(ev)}
    case OwnedExpr(e,d,o) => apply(e)(gc.push(d,Some(o)), a)
    case _ => applyDefault(exp)
  }
}
object OwnerSubstitutor {
  private def initGC(o: Expression, dom: Theory) = GlobalContext("").push(dom,Some(o))
  def apply(own: Expression, dom: Theory, d: Declaration): Declaration = {
    val os = new OwnerSubstitutor(true)
    os.apply(d)(initGC(own,dom),())
  }
  def apply(own: Expression, dom: Theory, tp: Type): Type = {
    val os = new OwnerSubstitutor(false)
    os.apply(tp)(initGC(own,dom),())
  }
  def apply(own: Expression, dom: Theory, e: Expression): Expression = {
    val os = new OwnerSubstitutor(false)
    os.apply(e)(initGC(own, dom),())
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
        case Some(ed: ExprDecl) if !ed.mutable && ed.dfO.isDefined => apply(ed.dfO.get)
        case _ => expR
      }
      case Application(BaseOperator(o,_), args) => Operator.simplify(o, args)
      case Projection(Tuple(es),i) => es(i)
      case ListElem(CollectionValue(es),IntValue(i)) => es(i.toInt)
      case Application(Lambda(vs,b), as) => Substituter(gc, vs.substitute(as), b)
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