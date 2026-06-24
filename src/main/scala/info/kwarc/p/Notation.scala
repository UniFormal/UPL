package info.kwarc.p

case class Notation(fixity: Fixity, symbol: String) {
  override def toString =  fixity + " " + symbol
}

/** Fixitis occur in 2 places:
  * - In [Notation]s that are attached to a constant (the target) of appropriate type.
  * - In [PseudoOperator]s applications (the source) that occur when parsing the use of an operator symbol.
  *
  * Such occurrences are then elaborated into a target application as follows:
  *
  * 1) The target's type is checked by matchTargetType.
  *    If this fails, it is an error in the declaration of the notation.
  *    Otherwise, it returns a list of types to be used for overloading resolution.
  * 2) The source's argument type and the expected return type are checked by matchSourceArguments.
  *    (In most cases, this simply calls arity to check the number of source arguments.)
  *    If this fails, it is an error in the use of the notation.
  *    Otherwise, it returns a list of types to be used during overloading resolution.
  * 3) The two lists are compared and the best target (if any) is chosen.
  *    This does not guarantee well-typedness but detects many common errors.
  * 4) elaborate is called on the target and the source arguments. The PseudoOperator is discarded.
  * 5) Type-checking continues on the elaboration result.
  *
  * Note that fixities may take arguments for handling flexary usages such as associativity rules.
  * These fields are meaningless in [PseudoOperator]s.
  * They only matter in [Notation]s.
  */
abstract class Fixity {
  /** to be used in error messages when the target's type doesn't match a notation */
  def expectedTargetAsString: String
  /** receives the target type and
    * returns the list of components that will be available for overloading resolution
    */
  def matchTargetType(tp: Type): Option[List[Type]]
  /** true for the possible numbers of arguments */
  def arity(n: Int): Boolean
  /** receives the types of the source arguments and the return type
    * returns an estimate for the type that the target must have
    * The returned type does not have to be well-formed.
    * It will only be compared for similarity with the type of the target constant.
    * Types that are not available are passed as null; null in the returned type is similar to any type.
    */
  def neededTargetType(ins: List[Type], out: Type): Type
  /** after matching to a target, elaborates the source arguments into an application of the target  */
  def elaborate(target: Expression, args: List[Expression]): Expression
  /** same as elaborate, but copies over the location from a non-empty argument list */
  protected def elaborateWithLocation(target: Expression, args: List[Expression]): Expression = {
     val e = elaborate(target, args)
     e.withLocationFromTo(args.head, args.last)
  }
}

object Fixity {
  /** parses concrete syntax into fixities */
  def parse(s: String) = {
    val f = s match {
      case "prefix" => Prefix
      case "postfix" => Postfix
      case "nullfix" => Nullfix
      case "infix" => Infix(NotAssociative)
      case "infix-left" => Infix(LeftAssociative)
      case "infix-right" => Infix(RightAssociative)
      case "infix-assoc" => Infix(Semigroup)
      case "circumfix-flex" => Circumfix(true)
      case "circumfix" => Circumfix(false)
      case "applyfix-flex" => Applyfix(true)
      case "applyfix" => Applyfix(false)
      case "bindfix-assoc" => Bindfix(true)
      case "bindfix" => Applyfix(false)
      case _ => null
    }
    Option(f)
  }
}

case object Nullfix extends Fixity {
  def expectedTargetAsString = "plain type without arguments"
  def matchTargetType(tp: Type) = Some(Nil)
  def neededTargetType(ins: List[Type], out: Type): Type = out
  def arity(n: Int) = n == 0
  def elaborate(target: Expression, args: List[Expression]) = target
}

/**
 * @param flex arguments are bundled into a list (assoc is ignored)
 * @param assoc if !flex, Some(true/false) iterating over arguments from the right/left
 */
case class Infix(assoc: Associativity = NotAssociative) extends Fixity {
  override def toString = {
    val q = assoc.toString
    "infix" + (if (q.nonEmpty) "-" else "") + q
  }
  def expectedTargetAsString = assoc match {
    case NotAssociative => "(a,b) -> c"
    case LeftAssociative | RightAssociative => "(a,a) -> a"
    case Semigroup | Monoid(_) => "List[a] -> a"
  }
  def matchTargetType(tp: Type) = (assoc,tp) match {
    case (Semigroup | Monoid(_), PlainFunType((_,CollectionType(a,_))::Nil, b)) => Some(List(a,b))
    case (_, PlainFunType((_,a)::(_,b)::Nil, c)) => Some(List(a,b,c))
    case _ => None
  }
  def arity(n: Int) = assoc match {
    case NotAssociative => n == 2
    case LeftAssociative | RightAssociative => n >= 2
    case Semigroup => n != 0
    case Monoid(_) => true
  }
  def neededTargetType(ins: List[Type], out: Type): Type = {
    val insN = assoc match {
      case Semigroup | _:Monoid => List(CollectionKind.List(ins.head))
      case _ => List(ins.head,ins.last)
    }
    SimpleFunType(insN,out)
  }
  def elaborate(target: Expression, args: List[Expression]) = {
    assoc match {
      case NotAssociative => Application(target, args)
      case Semigroup => Application(target, List(CollectionKind.List(args)))
      case Monoid(e) => args match {
        case Nil => e
        case List(a) => a
        case as => Application(target, List(CollectionKind.List(as)))
      }
      case LeftAssociative | RightAssociative => args match {
        case Nil => throw IError("arguments missing")
        case List(a) => a
        case _ =>
          val eArgs = if (assoc == LeftAssociative)
            List(args.head, elaborateWithLocation(target, args.tail))
          else
            List(elaborateWithLocation(target, args.init), args.last)
          Application(target, eArgs)
      }
    }
  }
}

trait PreOrPostfix extends Fixity {
  def expectedTargetAsString = "a -> b"
  def matchTargetType(tp: Type) = tp match {
    case PlainFunType((_,in)::Nil,out) => Some(List(in,out))
    case _ => None
  }
  def neededTargetType(ins: List[Type], out: Type): Type = SimpleFunType(ins,out)
  def arity(n: Int) = n == 1
  def elaborate(target: Expression, args: List[Expression]) = Application(target, args)
}

case object Prefix extends PreOrPostfix {
  override def toString = "prefix"
}

case object Postfix extends PreOrPostfix {
  override def toString = "postfix"
}

/**
 * @param flex arguments are bundled into a list
 */
case class Circumfix(flex: Boolean = false) extends Fixity {
  override def toString = {
    val q = if (flex) "-flex" else ""
    "circumfix" + q
  }
  def expectedTargetAsString = if (flex) "List[a] -> b" else "(a1,...) -> b"
  def matchTargetType(tp: Type) = tp match {
    case PlainFunType(args,out) =>
      if (flex) Some(args.map(_._2):::List(out))
      else args match {
        case (_,CollectionKind.List(a)) :: Nil => Some(List(a,out))
        case _ => None
      }
  }
  def arity(n: Int) = true
  def neededTargetType(ins: List[Type], out: Type): Type = {
    val insN = if (flex) List(CollectionKind.List(ins.head)) else ins
    SimpleFunType(insN,out)
  }
  def elaborate(target: Expression, args: List[Expression]) = {
    val eArgs = if (flex) List(CollectionKind.List(args)) else args
    Application(target, eArgs)
  }
}

/**
 * @param flex arguments are bundled into a list
 */
case class Applyfix(flex: Boolean = false) extends Fixity {
  override def toString = {
    val q = if (flex) "-flex" else ""
    "applyfix" + q
  }
  def expectedTargetAsString = if (flex) "(u,List[a]) -> b" else "(u,a1,...) -> b"
  def matchTargetType(tp: Type) = (flex,tp) match {
    case (true, PlainFunType((_,u)::(_,CollectionKind.List(a))::Nil, b)) => Some(List(u,a,b))
    case (false, PlainFunType(as,b)) => Some(as.map(_._2):::List(b))
    case _ => None
  }
  def arity(n: Int) = n != 0
  def neededTargetType(ins: List[Type], out: Type): Type = {
    val insN = if (flex) List(ins.head, CollectionKind.List(ins.tail.head)) else ins
    SimpleFunType(insN,out)
  }
  def elaborate(target: Expression, args: List[Expression]) = {
    val eArgs = if (flex) List(args.head, CollectionKind.List(args.tail)) else args
    Application(target, eArgs)
  }
}

/**
 * @param assoc multiple bindings are iterated
 */
case class Bindfix(assoc: Boolean = false) extends Fixity {
  override def toString = {
    val q = if (assoc) "-assoc" else ""
    "bindfix" + q
  }
  def expectedTargetAsString = if (assoc) "(a -> c) -> c" else "(a -> b) -> c"

  def matchTargetType(tp: Type) = tp match {
    case PlainFunType((_,PlainFunType(args,_))::Nil,c) => Some(List(args.head._2,c))
    case _ => None
  }
  def arity(n: Int) = n == 1
  /** exactly one function argument; extracts the variable types and the return type */
  def neededTargetType(ins: List[Type], out: Type): Type = ins.head match {
    case PlainFunType(args, o) => out<--(o<--(args.head._2))
    case _ => null
  }
  def elaborate(target: Expression, args: List[Expression]) = {
    if (!assoc) Application(target, args) else {
      val Lambda(vds, bd, _) :: Nil = args
      var r = bd
      // curry multiple bindings into single ones, innermost binding first
      vds.variables.foreach {vd =>
        val a = Lambda(vd, r).withLocationFromTo(vd, r)
        r = Application(target, List(a))
      }
      r
    }
  }
}

sealed abstract class Associativity
case object NotAssociative extends Associativity {
  override def toString = ""
}
case object Semigroup extends Associativity {
  override def toString = "assoc"
}
case class Monoid(neut: Expression) extends Associativity {
  override def toString = "assoc(" + neut + ")"
}
case object RightAssociative extends Associativity {
  override def toString = "right"
}
case object LeftAssociative extends Associativity {
  override def toString = "left"
}

// an operator whose fixity is not yet resolved
case class UnfixedOperator(symbol: String, loc: Location, spaceBefore: Int, spaceAfter: Int, opening: Boolean, closing: Boolean) {
  override def toString = symbol
  /** overriden to ignore location and spacing: equal if same symbol */
  override def equals(that: Any) = that match {
    case that: UnfixedOperator => this.symbol == that.symbol
    case _ => false
  }
  def attachLeft = spaceBefore < spaceAfter
  def attachRight = spaceBefore > spaceAfter
  def symmetric = spaceBefore == spaceAfter
  def unspaced = spaceBefore == 0 && spaceAfter == 0
  def precedence = spaceAfter + symbol.length + spaceBefore
  def withFixity(f: Fixity) = PseudoOperator(this, f)
  // Nullfix results in application to 0 arguments
  def toApplication(f: Fixity, args: List[Expression]) = {
    val op = withFixity(f).toExpression
    Application(op, args)
  }
}