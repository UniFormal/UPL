package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods */
abstract class Traverser[A] {

  def apply(p: Path)(implicit gc: GlobalContext, a: A): Path = matchC(p) {p => p}
  def apply(thy: Theory)(implicit gc: GlobalContext, a: A): Theory = matchC(thy) {thy =>
    if (thy == null) null else {
      val psT = thy.decls map apply
      Theory(psT)
    }
  }
  def apply(ctx: LocalContext)(implicit gc: GlobalContext, a:A): LocalContext = {
    if (ctx == null) null else matchC(ctx) {ctx =>
    val vdsT = ctx.decls map {d => apply(d).asInstanceOf[VarDecl]}
    LocalContext(vdsT)
  }}

  def apply(rc: RegionalContext)(implicit gc: GlobalContext, a:A): RegionalContext =
    RegionalContext(apply(rc.theory), rc.owner map apply, apply(rc.local))

  def apply(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = matchC(d)(applyDefault _)

  protected final def applyDefault(d: Declaration)(implicit gc: GlobalContext, a: A): Declaration = d match {
    case Module(n,op,ds) => Module(n, op, ds map {d => apply(d)(gc.enter(n),a)})
    case Include(dm,df, r) => Include(apply(dm), df map apply, r)
    case TypeDecl(n, bd, dfO) => TypeDecl(n, apply(bd), dfO map apply)
    case ExprDecl(n, tp, dfO, m) => ExprDecl(n, apply(tp), dfO map apply, m)
  }

  def apply(tp: Type)(implicit gc: GlobalContext, a: A): Type = matchC(tp)(applyDefault _)

  protected final def applyDefault(tp: Type)(implicit gc: GlobalContext, a: A): Type = tp match {
    case u: UnknownType => if (u.known) applyDefault(u.tp) else u // traversal eliminates unknown-wrappers
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
    case OwnedType(e, o) => OwnedType(apply(e), apply(o)(gc.push(RegionalContext(null,Some(e))),a))
    case b: BaseType => b
    case IntervalType(l,u) => IntervalType(l map apply, u map apply)
    case ClassType(thy) => ClassType(apply(thy))
    case ExprsOver(thy,q) => ExprsOver(apply(thy), apply(q)(gc.push(thy),a))
    case FunType(ts,t) => FunType(ts map apply, apply(t))
    case ProdType(ts) => ProdType(ts map apply)
    case CollectionType(b,k) => CollectionType(apply(b), k)
  }

  def apply(exp: Expression)(implicit gc: GlobalContext, a: A): Expression = matchC(exp)(applyDefault _)
  protected final def applyDefault(exp: Expression)(implicit gc: GlobalContext, a: A): Expression = exp match {
    case null => null
    case _: BaseValue => exp
    case _: VarRef => exp
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
    case OwnedExpr(o, e) => OwnedExpr(apply(o), apply(e)(gc.push(RegionalContext(null,Some(o))),a))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy) => Instance(apply(thy))
    case VarDecl(n,t,d,m,o) => VarDecl(n,apply(t), d map apply, m, o)
    case Assign(k,v) => Assign(apply(k), apply(v))
    case ExprOver(t,e) => ExprOver(apply(t), apply(e)(gc.push(t),a))
    case Eval(e) => Eval(apply(e))
    case Block(es) =>
      var lc = LocalContext.empty
      val esT = es.map {e =>
        val eT = apply(e)(gc.append(lc),a)
        e match {
          case vd: VarDecl => lc = lc.append(vd)
          case _ =>
        }
        eT
      }
      Block(esT)
    case IfThenElse(c, t, e) => IfThenElse(apply(c), apply(t), e map apply)
    case Match(e, cs, h) =>
      Match(apply(e), cs map {c => apply(c).asInstanceOf[MatchCase]}, h)
    case MatchCase(ctx,p,b) =>
      val gcI = if (ctx == null) gc else gc.append(ctx)
      MatchCase(apply(ctx), apply(p)(gcI,a), apply(b)(gc,a))
    case While(c,b) => While(apply(c), apply(b))
    case For(v,r,b) =>
      val vT = apply(v).asInstanceOf[VarDecl]
      For(vT, apply(r), apply(b)(gc.append(v),a))
    case Return(e, thrw) => Return(apply(e), thrw)
    case Lambda(is,b) =>
      val isT = apply(is)
      Lambda(isT, apply(b)(gc.append(is),a))
    case Application(f,as) => Application(apply(f), as map apply)
    case Tuple(es) => Tuple(es map apply)
    case Projection(e,i) => Projection(apply(e), i)
    case CollectionValue(es) => CollectionValue(es map apply)
    case ListElem(l,p) => ListElem(apply(l), apply(p))
    case Quantifier(q,vs,b) =>
      val vsT = apply(vs)
      Quantifier(q, vsT, apply(b)(gc.append(vs),a))
  }
}

abstract class StatelessTraverser extends Traverser[Unit]

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
  private def owners(implicit gc: GlobalContext) = gc.regions.collect {
    case r if r._2.owner.isDefined => r._2.owner.get
  }
  private def makeType(tp: Type)(implicit gc: GlobalContext) = {
    owners.foldLeft(tp) {case (sofar,next) => OwnedType(next, sofar)}
  }
  private def makeExpr(e: Expression)(implicit gc: GlobalContext) = {
    owners.foldLeft(e) {case (sofar,next) => OwnedExpr(sofar, next)}
  }
  override def apply(tp: Type)(implicit gc: GlobalContext, a: Unit) = if (shallow) makeType(tp) else matchC(tp) {
    case c: ClosedRef => makeType(c)
    case e: ExprsOver => makeType(e)
    case OwnedType(o,t) => apply(t)(gc.push(RegionalContext(null,Some(o))), a)
    case _ => applyDefault(tp)
  }
  override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = if (shallow) makeExpr(exp) else matchC(exp) {
    case c: ClosedRef => makeExpr(c)
    case e: ExprOver => EvalTraverser(e) {ev => apply(ev)}
    case OwnedExpr(e,o) => apply(e)(gc.push(RegionalContext(null,Some(o))), a)
    case _ => applyDefault(exp)
  }
}
object OwnerSubstitutor {
  private def initGC(o: Expression) = GlobalContext("").push(RegionalContext(null,Some(o)))
  def apply(own: Expression, d: Declaration): Declaration = {
    val os = new OwnerSubstitutor(true)
    os.apply(d)(initGC(own),())
  }
  def apply(own: Expression, tp: Type): Type = {
    val os = new OwnerSubstitutor(false)
    os.apply(tp)(initGC(own),())
  }
  def apply(own: Expression, e: Expression): Expression = {
    val os = new OwnerSubstitutor(false)
    os.apply(e)(initGC(own),())
  }
}

object Substitute extends Traverser[Substitution] {
  override def apply(exp: Expression)(implicit gc: GlobalContext, sub: Substitution) = matchC(exp) {
    case VarRef(n) => sub.lookupO(n) match {
      case None => exp
      case Some(vd) => vd.dfO.get
    }
    case vd: VarDecl =>
      super.apply(vd) // TODO: alpha-renaming
    case _ => applyDefault(exp)
  }
}

object Simplify extends StatelessTraverser {
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit): Expression = {
    val expR = applyDefault(exp) // first, recursively simplify subexpressions
    matchC(expR) {
      case Application(BaseOperator(o,_), args) => Operator.simplify(o, args)
      case Projection(Tuple(es),i) => es(i)
      case ListElem(CollectionValue(es),IntValue(i)) => es(i.toInt)
      case Application(Lambda(vs,b), as) => Substitute(b)(gc, vs.substitute(as))
      case e => e
    }
  }
}

private class FreeVariables(initGC: GlobalContext) extends StatelessTraverser {
  private var names: List[String] = Nil
  override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit) = matchC(exp) {
    case _:VarRef | _:ClosedRef if gc.regions.length == initGC.regions.length && gc.resolveName(exp).isEmpty =>
      val n = exp match {
        case VarRef(n) => n
        case ClosedRef(n) => n
        case _ => throw IError("impossible")
      }
      names ::= n
      VarRef(n)
    case _ => applyDefault(exp)
  }
}
object FreeVariables {
  def apply(gc: GlobalContext, e: Expression) = {
    val fv = new FreeVariables(gc)
    fv(e)(gc,())
    fv.names.distinct
  }
}