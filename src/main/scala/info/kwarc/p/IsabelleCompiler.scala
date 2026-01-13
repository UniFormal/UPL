package info.kwarc.p

import info.kwarc.p.IsabelleCompiler.compileIsabelle


class IsabelleCompiler(tv: TheoryValue) {
  def compileToIsa(): Isa = compileIsabelle(tv)

}

object IsabelleCompiler {

  def compileIsabelle(tv: TheoryValue): Isa = {
    // first and only declaration must be a module, ensured by checker?
    assert(tv.decls.length == 1 && tv.decls.head.isInstanceOf[Module])
    compileDecl(tv.decls.head)
  }

  def compileDecl(decl: Declaration): Isa = {
    decl match {
      case m: Module => IsaTheory(m, compileDecls(m.df.decls))
      case ed: ExprDecl => IsaDefiniton(ed)
    }
  }

  def compileDecls(decls: List[Declaration]): IsaBody = {
    IsaBody(decls.map(decl => compileDecl(decl)))
  }

}