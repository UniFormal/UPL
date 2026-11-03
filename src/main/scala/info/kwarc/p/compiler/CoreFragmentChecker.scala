package info.kwarc.p.compiler

import info.kwarc.p.SyntaxFragment.matchC
import info.kwarc.p._

/** A traverser that fails if it encounters any code fragments that are not supported by the core compiler fragment. */
object CoreFragmentChecker extends Traverser[CoreFragmentContext] {

  private def fail(msg: String) = IError(s"Unsupported code fragment: $msg")

  override def apply(tp: Type)(implicit gc: GlobalContext, ctx: CoreFragmentContext): Type = {
    matchC(tp) { case NumberType(neg, frac, im, approx, infinite) => if (im) {
      throw fail(s"Imaginary number type: $tp")
    }
      if (frac && !approx) { // Some numbers may be approximated, even though they shouldn't be
        // throw fail(s"Accurate fraction: $tp")
      }
      applyDefault(tp)
    case _ => applyDefault(tp)
    }
  }
}

case class CoreFragmentContext() {}
