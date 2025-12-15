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


     var noChanges : Boolean = false
     while(!noChanges) {
       noChanges = true

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
         println(p, us, us.length, us.flatMap(u => List((u.name, (p.occursRight:::p.occursLeft).count(s => s == u.name)))))

         if (us.length == 1 && (p.occursRight:::p.occursLeft).iterator.count(s => s == us.head.name) == 1) {
           val u = us.head
           // unknown == f(knowns)
           p.definiendum match {
             case Some(u.name) => {
               knowns ::= Known(u.name, p.right, true)
               unknowns = unknowns.filter(x => x.name != u.name)
               noChanges = false
               redundantP = p::redundantP
             }
             // f(knowns) == unknown
             case Some(_) | None => p.reverseDefinendum match {
               case Some(u.name) =>  {
                 knowns ::= Known(u.name, p.left, true)
                 unknowns = unknowns.filter(x => x.name != u.name)
                 noChanges = false
                 redundantP = p::redundantP
               }
               // other forms
               // TODO umformungen
               case Some(_) | None => {
                 val iso = findIsolatable(p.left, Occurrence.root.path).filter(n => n._1 == u.name)
                 Console.println(iso)
                 //Console.println(InverseMethods.all.foreach(m => m.apply(p.left, p.right)))
                 iso match {
                   case Nil =>
                   case iso_head :: rest =>
                     // TODO andere Optionen aus rest???
                     val newProp = isolate(p, iso_head._2)
                     props ::= newProp
                     knowns ::= Known(u.name, newProp.right, true)
                     unknowns = unknowns.filter(x => x.name != u.name)
                     noChanges = false
                 }
               }
             }
           }
         }
       })
     }

     // TODO #unknowns in axiom/thy > 1


     println("---------")
     printAsTheory("Unknowns", unknowns)
     printAsTheory("Knowns", knowns)
     printAsTheory("Properties", props)
     printAsTheory("Redundant", redundantP)


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
     println(changed)
     if (changed) TheoryValue(declsE).copyFrom(thy)
     else thy
   }

  /**
   * finds all possibilities which unknowns can be isolated where
   * @param e current expression to traverse
   * @param traversed: accumulator of path traversed so far
   */
  def findIsolatable(e: Expression, traversed: List[Int]): List[(String,Occurrence)] = e match {
    case ClosedRef(n) => List((n, Occurrence(traversed.reverse)))
    case Application(BaseOperator(op,_), as) =>
      op.isolatableArguments.flatMap(i => findIsolatable(as(i), i::traversed))
    case Application(OpenRef(p), as) =>
      InverseMethods.findIsolatable(p, as, traversed)
      // TODO InverseMethods.all.filter(im => im.fun.eq(p)).flatMap(im => ())
    case Tuple(es) =>
      Range(0,es.length).toList.flatMap(i => findIsolatable(es(i), i::traversed))
    case _ => Nil
  }

  /**
   * rearranges a property so that it isolates at an occurrence in the left expression
   */
  def isolate(prop: Property, at: Occurrence): Property = {
    at.path match {
      case Nil => prop
      case i :: rest =>
        val lrO = prop.left match {
          case Application(BaseOperator(op, _), as) => op.isolate(i, as, prop.right)
          case Application(OpenRef(p), as) => InverseMethods.isolate(i, p, prop)
          case _ => None
        }
        val (l,r) = lrO.get
        isolate(Property(l,r),Occurrence(rest))
    }
  }

  def printAsTheory(name: String, theorylike: List[Any]): Unit = {
    println(name + ":{\n" + theorylike.mkString("\n").indent(2) + "}")
  }
}

case class Occurrence(path: List[Int]) {
  def and(i: Int) = copy(i::path)
}
object Occurrence {
  val root = Occurrence(Nil)
}

case class Unknown(name: String, tp: Type){
  override def toString = s"$name : $tp"}

case class Known(name: String, df: Expression, isNew: Boolean) {
  val uses = Regionals(df)._1
  override def toString = s"$name = $df"
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

  override def toString = s"|- $left == $right"
}

abstract class InverseMethodData(fun: Path, argPos: Int) {
  def apply(l: Expression, r: Expression): Option[(Expression,Expression)]
  def findIsolatable(p: Path, args: List[Expression], traversed: List[Int]): List[(String, Occurrence)]
}

case class InverseUnary(fun: Path, inv: Path) extends InverseMethodData (fun, 0) {
  def apply(l: Expression, r: Expression): Option[(Expression,Expression)] = {
    l match {
      case Application(OpenRef(q), List(a)) if fun.toString().equals(q.toString) => Some((a,Application(OpenRef(inv), List(r))))
      case _ => None
    }
  }

  def findIsolatable(p: Path, args: List[Expression], traversed: List[Int]): List[(String, Occurrence)] = {
    if (fun.toString().equals(p.toString())) {
      Solver.findIsolatable(args(0), 0 :: traversed)
    }
    else {
      Nil
    }
  }
}

// TODO InverseBinaryLeft
//case class InverseBinaryLeft(fun: Path, inv: Path) extends InverseMethodData(fun, 1) {
  //def apply(l: Expression, r: Expression): Option[(Expression,Expression)] = {
   // l match {
   //   case Application(OpenRef(q), List(a)) if fun == q => Some((a,Application(OpenRef(inv), List(r))))
  //  }
  //}
//}
// TODO InverseBinaryRight

object InverseMethods {
  val all = List(
    InverseUnary(Path("Math.sin"), Path("Math.asin")),
    InverseUnary(Path("Math.cos"), Path("Math.acos")),
    InverseUnary(Path("Math.tan"), Path("Math.atan")),
    InverseUnary(Path("Math.asin"), Path("Math.sin")),
    InverseUnary(Path("Math.acos"), Path("Math.cos")),
    InverseUnary(Path("Math.atan"), Path("Math.tan")),
    InverseUnary(Path("Math.exp"), Path("Math.ln")),
    InverseUnary(Path("Math.sqrt"), Path("Math.pow2")),
    InverseUnary(Path("Math.pow2"), Path("Math.sqrt")),
    InverseUnary(Path("Math.toDegrees"), Path("Math.toRadians"))
  )

  def findIsolatable(fun: Path, args: List[Expression], traversed: List[Int]): List[(String,Occurrence)] = {
    Console.println("fI: ", fun, args)
    all.flatMap(f => f.findIsolatable(fun, args, traversed))
  }

  def isolate(i: Int, p: Path, prop: Property): Option[(Expression, Expression)] = {
    all.filter(f => f.fun.toString.equals(p.toString())).head.apply(prop.left, prop.right)
    //val iu = all.filter(f => f.fun.eq(p))
    //iu match {
    //  case Nil =>
    //  case i :: rest => i.apply()
    //}
  }
  // --> apply
}

object SolverTest {
  def main(args: Array[String]): Unit = {
    val path = File(args(0)).canonical
    val proj = Project.fromFile(path, None)
    val voc = proj.check(true)
    val gc = GlobalContext(voc)
    val tS = Solver.solve(gc, OpenRef(Path("SolverTest", "Test2")))
    println(tS)
  }
}