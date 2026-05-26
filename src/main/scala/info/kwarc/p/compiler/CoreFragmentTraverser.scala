package info.kwarc.p.compiler

import info.kwarc.p.SyntaxFragment.matchC
import info.kwarc.p.{
  Declaration,
  Expression,
  GlobalContext,
  IError,
  Lambda,
  NumberType,
  Theory,
  Traverser,
  Type
}

/** A traverser that fails if it encounters any code fragments that are not supported by the core compiler fragment.
  */
object CoreFragmentTraverser extends Traverser[Context] {

  override def apply(
      exp: Expression
  )(implicit gc: GlobalContext, ctx: Context): Expression = {
    val nCtx = ctx.copy(declared = false)
    matchC(exp) {
      case Lambda(_, _, _) =>
        if (!ctx.declared) {
          throw fail(s"Anonymous lambda: '$exp'")
        }
        applyDefault(exp)(gc, nCtx)
      case _ => applyDefault(exp)(gc, nCtx)
    }
  }

  override def apply(
      thy: Theory
  )(implicit gc: GlobalContext, ctx: Context): Theory = {
    val nCtx = ctx.copy(declared = false)
    matchC(thy) { case _ =>
      applyDefault(thy)(gc, nCtx)
    // throw fail(s"Theory: $thy")
    }
  }

  override def apply(
      tp: Type
  )(implicit gc: GlobalContext, ctx: Context): Type = {
    val nCtx = ctx.copy(declared = false)
    matchC(tp) {
      case NumberType(neg, frac, im, approx, infinite) =>
        if (im) {
          throw fail(s"Imaginary number type: $tp")
        }
        if (frac && !approx) {
          // Some numbers may be approximated, even though they shouldn't be
          // throw fail(s"Accurate fraction: $tp")
        }
        applyDefault(tp)(gc, nCtx)
      case _ =>
        applyDefault(tp)(gc, nCtx)
    }
  }

  private def fail(msg: String) = IError(s"Unsupported code fragment: $msg")

  override def apply(
      decl: Declaration
  )(implicit gc: GlobalContext, ctx: Context): Declaration = {
    val nCtx = ctx.copy(declared = true)
    matchC(decl) { case _ =>
      applyDefault(decl)(gc, nCtx)
    }
  }
}

case class Context(var declared: Boolean = false) {}
