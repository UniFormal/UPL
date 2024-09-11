package info.kwarc.p

import SyntaxFragment.matchC

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods */
abstract class Traverser[A] {

  def apply(p: Path)(implicit a: A): Path = matchC(p) {p => p}
  def apply(thy: Theory)(implicit a: A): Theory = matchC(thy) {thy =>
    if (thy == null) null else {
      val psT = thy.parts map {case Inclusion(p,dfO) => Inclusion(apply(p), dfO map apply)}
      Theory(psT)
    }
  }
  def apply(ctx: Context)(implicit a:A): Context = matchC(ctx) {ctx =>
    val vdsT = ctx.decls map {case VarDecl(n,tp,df,m) => VarDecl(n, apply(tp), df map apply, m)}
    Context(vdsT)
  }

  def apply(d: Declaration)(implicit a: A): Declaration = matchC(d)(applyDefault _)

  protected final def applyDefault(d: Declaration)(implicit a: A): Declaration = d match {
    case Module(n,op,ds) => Module(n, op, ds map apply)
    case Vocabulary(ds) => Vocabulary(ds map apply)
    case Include(dm,df) => Include(apply(dm), df map apply)
    case TypeDecl(n, bd, dfO) => TypeDecl(n, apply(bd), dfO map apply)
    case ExprDecl(n, tp, dfO) => ExprDecl(n, apply(tp), dfO map apply)
  }

  def apply(tp: Type)(implicit a: A): Type = matchC(tp)(applyDefault _)

  protected final def applyDefault(tp: Type)(implicit a: A): Type = tp match {
    case null => null // in case we traverse before inferring types
    case TypeRef(p) => TypeRef(apply(p))
    case TypeFieldRef(o,f) => TypeFieldRef(o map apply, f)
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
    case SymbolRef(p) => SymbolRef(apply(p))
    case BaseOperator(o,tp) => BaseOperator(o, apply(tp))
    case Instance(thy, ds) => Instance(apply(thy), ds map {d => apply(d).asInstanceOf[SymbolDeclaration]})
    case FieldRef(o,n) => FieldRef(o map apply, n)
    case InstanceWith(e, p) => InstanceWith(apply(e), apply(p))
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

class OwnerSubstitutor(own: Expression) extends Traverser[Int] {
  var substituted = false
  override def apply(d: Declaration)(implicit i: Int) = matchC(d) {
    case ad: AtomicDeclaration if i == 0 && ad.dfO.isEmpty =>
      substituted = true
      val dT = applyDefault(ad)
      val sown = Some(own)
      ad match {
        case d: ExprDecl => dT.asInstanceOf[ExprDecl].copy(dfO = Some(FieldRef(sown,d.name)))
        case d: TypeDecl => dT.asInstanceOf[TypeDecl].copy(dfO = Some(TypeFieldRef(sown,d.name)))
        case _: Include =>  dT.asInstanceOf[Include] .copy(dfO = sown)
      }
    case _ => applyDefault(d)
  }
  override def apply(tp: Type)(implicit i: Int) = matchC(tp) {
    case TypeFieldRef(None,f) if i == 0 =>
      substituted = true
      TypeFieldRef(Some(own), f)
    case _ => applyDefault(tp)
  }
  override def apply(exp: Expression)(implicit i: Int) = matchC(exp) {
    case FieldRef(None, f) if i == 0 => FieldRef(Some(own), f)
    case _:ExprOver => applyDefault(exp)(i+1)
    case _:Eval => applyDefault(exp)(i-1)
    case _ => applyDefault(exp)
  }
}
object OwnerSubstitutor {
  def apply(own: Expression, d: Declaration): Declaration = {
    val os = new OwnerSubstitutor(own)
    os.apply(d)(0)
  }
  def apply(own: Expression, tp: Type): Type = {
    val os = new OwnerSubstitutor(own)
    os.apply(tp)(0)
  }
  def apply(own: Expression, e: Expression): Expression = {
    val os = new OwnerSubstitutor(own)
    os.apply(e)(0)
  }
}