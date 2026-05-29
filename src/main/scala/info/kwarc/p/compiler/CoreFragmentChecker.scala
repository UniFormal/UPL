package info.kwarc.p.compiler

import info.kwarc.p.SyntaxFragment.matchC
import info.kwarc.p._

/** A traverser that fails if it encounters any code fragments that are not supported by the core compiler fragment. */
object CoreFragmentChecker extends Traverser[CoreFragmentContext] {

  override def apply(exp: Expression)(implicit gc: GlobalContext, ctx: CoreFragmentContext): Expression = {
    val nCtx = ctx.copy(declared = false)
    matchC(exp) { case Lambda(ins, body, mayReturn) => if (!ctx.declared) {
      throw fail(s"Anonymous lambda: '$exp'")
    }
      body match {
        case application: Application => if (ins.variables.size != application.args.size) {
          throw fail(s"Closure lambda: '$exp'")
        }
        case _ =>
      }

      applyDefault(exp)(gc, nCtx)
    case _: Instance => if (!ctx.declared) {
      throw fail(s"Anonymous theory: '$exp'")
    }
      applyDefault(exp)(gc, nCtx)
    case _ => applyDefault(exp)(gc, nCtx)
    }
  }

  private def fail(msg: String) = IError(s"Unsupported code fragment: $msg")

  override def apply(thy: Theory)(implicit gc: GlobalContext, ctx: CoreFragmentContext): Theory = {
    val nCtx = ctx.copy(declared = false)
    matchC(thy) { case TheoryValue(decls) => val includedNames = decls.flatMap { case Include(OpenRef(p), _, _) => gc
      .lookupGlobal(p) match {
      case Some(Module(_, _, df)) => df.decls.filter(d => d.isInstanceOf[NamedDeclaration]).map(d => d.nameO.get)
    }
    case _ => List()
    }.toSet
      decls.foreach { case ExprDecl(declName, _, _, _, _, _) => if (!includedNames.contains(declName))
        throw fail(s"Extended theory. Introduces expression '$declName' that wasn't declared in any included theory: '$thy'")
      case _ =>
      }
      applyDefault(thy)(gc, nCtx)
    case _ => applyDefault(thy)(gc, nCtx)
    }
  }

  override def apply(tp: Type)(implicit gc: GlobalContext, ctx: CoreFragmentContext): Type = {
    val nCtx = ctx.copy(declared = false)
    matchC(tp) { case NumberType(neg, frac, im, approx, infinite) => if (im) {
      throw fail(s"Imaginary number type: $tp")
    }
      if (frac && !approx) { // Some numbers may be approximated, even though they shouldn't be
        // throw fail(s"Accurate fraction: $tp")
      }
      applyDefault(tp)(gc, nCtx)
    case _ => applyDefault(tp)(gc, nCtx)
    }
  }

  override def apply(decl: Declaration)(implicit gc: GlobalContext, ctx: CoreFragmentContext): Declaration = {
    val nCtx = ctx.copy(declared = true)
    matchC(decl) { case _ => applyDefault(decl)(gc, nCtx)
    }
  }
}

case class CoreFragmentContext(var declared: Boolean = false) {}
