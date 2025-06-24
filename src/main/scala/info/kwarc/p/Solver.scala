package info.kwarc.p

object Solver {
   val checker = new Checker(ErrorThrower)
   case class Error(msg: String, thy: Theory) extends SError(thy.loc, msg + " while solving " + thy)
   def fail(msg: String)(implicit thy: Theory) = throw Error(msg, thy)

   /**
    * conservatively extends a theory, trying to reduce the abstract interface
    * e.g., by adding definitions for symbols that are determined by axioms
    */
   def solve(gc: GlobalContext, thy: Theory) = {
     implicit val cause = thy
     val thyE = Checker.evaluateTheory(gc, thy)
     val thyN = checker.Normalize(gc,thyE)
     // the state during solving
     var unknowns: List[Unknown] = Nil  // expression symbol we can still solve
     var knowns: List[Known] = Nil      // expression symbol we have solved
     var props: List[Property] = Nil    // axioms/theorems we can still use
     var redundant: List[String] = Nil  // axioms/theorems that we have used and that should be removed from the theory
     var redundantP: List[Property] = Nil
     // prepare the solving by collecting the relevant information from the theory
     thyN.decls foreach {
       case _: Include =>
          // include in normalized theory can be ignored
       case td: TypeDecl =>
         if (!td.defined) fail("abstract type fields not supported: " + td.name)
       case thd: Module =>
         fail("nested theories not supported: " + thd.name)
       case ed: ExprDecl =>
         ed.tp match {
           case ProofType(Equality(true,_,l,r)) =>
             props ::= Property(l,r)
           case _ =>
             if (!ed.defined)
               unknowns ::= Unknown(ed.name, ed.tp)
             else
               knowns ::= Known(ed.name, ed.dfO.get, false)
         }

     }



     // the actual solving
     // TODO

     println(thyN.decls.filter(d => !d.defined))
     println(thyN.decls.filter(d => d.defined))


     // TODO remove redundant axioms
     props.foreach(p => {
       if (p.occursRight.appendedAll(p.occursLeft).forall(s => knowns.exists(k => k.name == s))) {
          redundantP ::= p
         // TODO check axiom eval true ??
       }
     })

     // TODO #unknowns in axiom/thy = 1
     props.filter(p => !redundantP.contains(p)).foreach(p => {
       val us = unknowns.filter(u => (p.occursRight:::p.occursLeft).contains(u.name))
       println(p, us, us.length)
       if (us.length == 1) {
         // unknown == f(knowns)
         // TODO check dass die unbekannte nur auf der einen seite
         p.definiendum match {
           case None =>
           case Some(s) => knowns ::= Known(s, p.right, true)
         }
         // f(knowns) == unknown
         p.reverseDefinendum match {
           case None =>
           case Some(s) => knowns ::= Known(s, p.left, true)
         }
         // other forms
         // TODO umformungen
       }
     })
     // TODO #unknowns in axiom/thy > 1


     println("---------")
     println("U:", unknowns)
     println("K:", knowns)
     println("R:", redundantP)
     println("P:", props)




     // just for temporary testing: add one definition
     //knowns ::= Known("a", IntValue(1), true)

     // return the extended theory by adding definitions and dropping now-redundant properties
     var changed = false
     val declsE = thyN.decls flatMap {
       case ed: ExprDecl =>
         if (redundant.exists(_ == ed.name))
           Nil


         else {
           knowns.find(k => k.name == ed.name && k.isNew) match {
             case Some(k) =>
               changed = true
               List(ed.copy(dfO = Some(k.df)))
             case _ =>
               List(ed)
           }
         }
       case d => List(d)
     }
     if (changed) TheoryValue(declsE).copyFrom(thy)
     else thy
   }
}

case class Unknown(name: String, tp: Type)

case class Known(name: String, df: Expression, isNew: Boolean) {
  val uses = Regionals(df)._1
}

case class Property(left: Expression, right: Expression) {
  val occursLeft = Regionals(left)._1
  val occursRight = Regionals(right)._1
  def definiendum = left match {
    case ClosedRef(n) => Some(n)
    case _ => None
  }
  def reverseDefinendum = right match {
    case ClosedRef(n) => Some(n)
    case _ => None
  }
}

object SolverTest {
  def main(args: Array[String]): Unit = {
    val path = File(args(0)).canonical
    val proj = Project.fromFile(path, None)
    proj.check(true)
    val gc = proj.makeGlobalContext
    val tS = Solver.solve(gc, OpenRef(Path("SolverTest", "T")))
    println(tS)
  }
}