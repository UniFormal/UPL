package info.kwarc.p.compiler

import info.kwarc.p.SyntaxFragment.matchC
import info.kwarc.p.{
  ExprDecl,
  Expression,
  GlobalContext,
  IError,
  Include,
  Lambda,
  Module,
  NamedDeclaration,
  OpenRef,
  Quantifier,
  StatelessTraverser,
  Theory,
  TheoryValue
}

object CoreFragmentTraverser extends StatelessTraverser {
  override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit): Expression = matchC(exp) {
    case Quantifier(univ, vars, body) =>
      fail(s"quantifier can't be compiled")
      applyDefault(exp)
    case Lambda(ins, body, mayReturn) =>
      val declaredExpressions = gc.parentDecls.flatMap {
        case ExprDecl(_, _, _, dfO, _, _) =>
          dfO
        case _ => None
      }

      if (!declaredExpressions.contains(exp)) {
        fail(s"anonymous lambda '$exp'")
      }
      applyDefault(exp)
    case _ => applyDefault(exp)
  }

  override def apply(thy: Theory)(implicit gc: GlobalContext, a: Unit): Theory = matchC(thy) {
    case TheoryValue(decls) =>
      val declaredNames = decls.flatMap {
        case Include(OpenRef(p), _, _) =>
          gc.lookupGlobal(p) match {
            case Some(Module(_, _, df)) =>
              df.decls.filter(d => d.isInstanceOf[NamedDeclaration]).map(d => d.nameO.get)
          }
        case _ => List()
      }.toSet

      decls.foreach {
        case ExprDecl(name, _, _, _, _, _) =>
          if (!declaredNames.contains(name))
            fail(s"anonymous theory. introduces undeclared expression '$name'")
        case _ =>
      }

      applyDefault(thy)
    case _ => applyDefault(thy)
  }

  def fail(msg: String): Unit = {
    throw IError(s"Unsupported code fragment: $msg")
  }
}