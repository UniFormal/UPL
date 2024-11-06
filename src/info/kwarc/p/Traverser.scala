package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods */
abstract class Traverser[A] {

  def apply(p: Path)(implicit a: A): Path = matchC(p) {p => p}
  def apply(thy: Theory)(implicit a: A): Theory = matchC(thy) {thy =>
    if (thy == null) null else {
      val psT = thy.parts map apply
      Theory(psT)
    }
  }
  def apply(ctx: Context)(implicit a:A): Context = matchC(ctx) {ctx =>
    val vdsT = ctx.decls map {case VarDecl(n,tp,df,m) => VarDecl(n, apply(tp), df map apply, m)}
    Context(vdsT)
  }
  def apply(env: LocalEnvironment)(implicit a:A): LocalEnvironment = LocalEnvironment(apply(env.theory), apply(env.context))

  def apply(d: Declaration)(implicit a: A): Declaration = matchC(d)(applyDefault _)

  protected final def applyDefault(d: Declaration)(implicit a: A): Declaration = d match {
    case Module(n,op,ds) => Module(n, op, ds map apply)
    case Include(dm,df, r) => Include(apply(dm), df map apply, r)
    case TypeDecl(n, bd, dfO) => TypeDecl(n, apply(bd), dfO map apply)
    case ExprDecl(n, tp, dfO, m) => ExprDecl(n, apply(tp), dfO map apply, m)
  }

  def apply(tp: Type)(implicit a: A): Type = matchC(tp)(applyDefault _)

  protected final def applyDefault(tp: Type)(implicit a: A): Type = tp match {
    case u: UnknownType => if (u.known) applyDefault(u.tp) else u // traversal eliminates unknown-wrappers
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
    case OwnedType(e, o) => OwnedType(apply(e), apply(o))
    case b: BaseType => b
    case ClassType(thy) => ClassType(apply(thy))
    case ExprsOver(thy,q) => ExprsOver(apply(thy), apply(q))
    case FunType(ts,t) => FunType(ts map apply, apply(t))
    case ProdType(ts) => ProdType(ts map apply)
    case ListType(t) => ListType(apply(t))
    case OptionType(t) => OptionType(apply(t))
  }

  def apply(exp: Expression)(implicit a: A): Expression = matchC(exp)(applyDefault _)
  protected final def applyDefault(exp: Expression)(implicit a: A): Expression = exp match {
    case null => null
    case _: BaseValue => exp
    case _: VarRef => exp
    case ClosedRef(n) => ClosedRef(n)
    case OpenRef(p) => OpenRef(apply(p))
    case OwnedExpr(o, e) => OwnedExpr(apply(o), apply(e))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy, ds) => Instance(apply(thy), ds map {d => apply(d).asInstanceOf[SymbolDeclaration]})
    case VarDecl(n,t,d,m) => VarDecl(n,apply(t), d map apply, m)
    case Assign(k,v) => Assign(apply(k), apply(v))
    case ExprOver(t,e) => ExprOver(apply(t), apply(e))
    case Eval(e) => Eval(apply(e))
    case Block(es) => Block(es map apply)
    case IfThenElse(c, t, e) => IfThenElse(apply(c), apply(t), e map apply)
    case While(c,b) => While(apply(c), apply(b))
    case For(n,r,b) => For(n,apply(r), apply(b))
    case Lambda(is,b) => Lambda(apply(is), apply(b))
    case Application(f,as) => Application(apply(f), as map apply)
    case Tuple(es) => Tuple(es map apply)
    case Projection(e,i) => Projection(apply(e), i)
    case ListValue(es) => ListValue(es map apply)
    case ListElem(l,p) => ListElem(apply(l), apply(p))
    case OptionValue(e) => if (e == null) exp else OptionValue(apply(e))
  }
}

abstract class StatelessTraverser extends Traverser[Unit]

object IdentityTraverser extends StatelessTraverser

class EvalTraverser(cont: Expression => Expression) extends Traverser[Int] {
  override def apply(exp: Expression)(implicit level: Int) = matchC(exp) {
    case ExprOver(s, t) => applyDefault(exp)(level+1)
    case Eval(e) => if (level==0) cont(e) else applyDefault(exp)(level-1)
    case _ => applyDefault(exp)
  }
}
object EvalTraverser {
  def apply(e: ExprOver)(cont: Expression => Expression) = new EvalTraverser(cont).apply(e.expr)(0)
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
    (Context(evals.reverse), eoT)
  }
}

class OwnerSubstitutor(shallow: Boolean) extends Traverser[List[Expression]] {
  private def makeType(tp: Type)(implicit os: List[Expression]) = {
    os.foldLeft(tp) {case (sofar,next) => OwnedType(next, sofar)}
  }
  private def makeExpr(e: Expression)(implicit os: List[Expression]) = {
    os.foldLeft(e) {case (sofar,next) => OwnedExpr(sofar, next)}
  }
  override def apply(tp: Type)(implicit os: List[Expression]) = if (shallow) makeType(tp) else matchC(tp) {
    case c: ClosedRef => makeType(c)
    case e: ExprsOver => makeType(e)
    case OwnedType(o,t) => apply(t)(o::os)
    case _ => applyDefault(tp)
  }
  override def apply(exp: Expression)(implicit os: List[Expression]) = if (shallow) makeExpr(exp) else matchC(exp) {
    case c: ClosedRef => makeExpr(c)
    case e: ExprOver => EvalTraverser(e) {ev => apply(ev)(os)}
    case OwnedExpr(e,o) => apply(e)(o::os)
    case _ => applyDefault(exp)
  }
}
object OwnerSubstitutor {
  def apply(own: Expression, d: Declaration): Declaration = {
    val os = new OwnerSubstitutor(true)
    os.apply(d)(List(own))
  }
  def apply(own: Expression, tp: Type): Type = {
    val os = new OwnerSubstitutor(false)
    os.apply(tp)(List(own))
  }
  def apply(own: Expression, e: Expression): Expression = {
    val os = new OwnerSubstitutor(false)
    os.apply(e)(List(own))
  }
}