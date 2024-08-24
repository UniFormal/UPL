package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods */
abstract class Traverser[A] {

  def apply(p: Path)(implicit a: A): Path = matchC(p) {p => p}
  def apply(thy: Theory)(implicit a: A): Theory = matchC(thy) {thy =>
    if (thy == null) null else Theory(thy.parts map apply)
  }
  def apply(ctx: Context)(implicit a:A): Context = matchC(ctx) {ctx =>
    val vdsT = ctx.decls map {case VarDecl(n,tp,df,m) => VarDecl(n, apply(tp), df map apply, m)}
    Context(vdsT)
  }

  def apply(d: Declaration)(implicit a: A): Declaration = matchC(d)(applyDefault _)

  protected final def applyDefault(d: Declaration)(implicit a: A): Declaration = d match {
    case Module(n,op,ds) => Module(n, op, ds map apply)
    case Vocabulary(ds) => Vocabulary(ds map apply)
    case Include(dm,df,r) => Include(apply(dm), df map apply, r)
    case TypeDecl(n,dfO) => TypeDecl(n, dfO map apply)
    case SymDecl(n, tp, dfO) => SymDecl(n, apply(tp), dfO map apply)
  }

  def apply(tp: Type)(implicit a: A): Type = matchC(tp)(applyDefault _)

  protected final def applyDefault(tp: Type)(implicit a: A): Type = tp match {
    case null => null // in case we traverse before inferring types
    case TypeRef(p) => TypeRef(apply(p))
    case b: BaseType => b
    case ClassType(thy) => ClassType(apply(thy))
    case ExprsOver(thy,q) => ExprsOver(apply(thy), apply(q))
    case FunType(ts,t) => FunType(ts map apply, apply(t))
    case ProdType(ts) => ProdType(ts map apply)
    case ListType(t) => ListType(apply(t))
  }

  def apply(exp: Expression)(implicit a: A): Expression = matchC(exp)(applyDefault _)
  protected final def applyDefault(exp: Expression)(implicit a: A): Expression = exp match {
    case _: BaseValue => exp
    case _: VarRef => exp
    case SymbolRef(p) => SymbolRef(apply(p))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy, ds) => Instance(apply(thy), ds map apply)
    case FieldRef(o,n) => FieldRef(o map apply, n)
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
  }
}

abstract class StatelessTraverser extends Traverser[Unit]

object IdentityTraverser extends StatelessTraverser