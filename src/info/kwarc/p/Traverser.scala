package info.kwarc.p

import SyntaxFragment.keepRef

/** syntax traverser
  * to use this, override the apply methods, implement the relevant cases, and call applyDefault for everything else
  * applyDefault will traverse the AST one step and then recurse back into the respective apply methods */
abstract class Traverser[A] {

  def apply(d: Declaration)(implicit a: A): Declaration = applyDefault(d)

  protected final def applyDefault(d: Declaration)(implicit a: A): Declaration = keepRef(d) {
    case Module(n,op,ds) => Module(n, op, ds map apply)
    case TypeDecl(n,dfO) => TypeDecl(n, dfO map apply)
    case SymDecl(n, tp, dfO) => SymDecl(n, apply(tp), dfO map apply)
  }

  def apply(p: Path)(implicit a: A) = keepRef(p) {p => p}

  def apply(tp: Type)(implicit a: A): Type = applyDefault(tp)

  def apply(thy: Theory)(implicit a: A) = Theory(thy.parts map apply)

  protected final def applyDefault(tp: Type)(implicit a: A): Type = keepRef(tp) {
    case null => null
    case TypeRef(p) => TypeRef(apply(p))
    case ClassType(thy) => ClassType(apply(thy))
    case b: BaseType => b
    case ExprsOver(thy,q) => ExprsOver(apply(thy), apply(q))
    case FunType(ts,t) => FunType(ts map apply, apply(t))
    case ProdType(ts) => ProdType(ts map apply)
    case ListType(t) => ListType(apply(t))
  }

  def apply(exp: Expression)(implicit a: A): Expression = applyDefault(exp)
  protected final def applyDefault(exp: Expression)(implicit a: A): Expression = exp match {
    case e: BaseValue => e
  }
}

abstract class StatelessTraverser extends Traverser[Unit] {

}

object IdentityTraverser extends StatelessTraverser