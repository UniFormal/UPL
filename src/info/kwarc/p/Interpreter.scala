package info.kwarc.p

case class FrameEntry(name: String, var value: Expression) {
  override def toString = name + " = " + value
}
/** @param owner the object relative to which names are to be interpreted,
  *  e.g., the class in which the currently interpreted function is declared
  *        empty if some other function is interpreted
  * @param vars the visible local variables
  *  e.g., the arguments of the called function
  */
case class Frame(name: String, owner: Option[Structure], var vars: List[FrameEntry]) {
  override def toString = name + ": " + owner + vars.mkString(", ")
  def lookup(n: String) = vars.find(_.name == n) match {
    case Some(f) => f.value
    case None => throw IError("variable does not exist: " + n)
  }
  def update(n: String, v: Expression) {
    vars.find(_.name == n).get.value = v
  }
  def add(n: String, vl: Expression) {
    vars ::= FrameEntry(n, vl)
    addedInBlock = (addedInBlock.head + 1) :: addedInBlock.tail
  }

  private var addedInBlock: List[Int] = Nil
  def enterBlock {
    addedInBlock ::= 0
  }
  def leaveBlock {
    vars = vars.drop(addedInBlock.head)
    addedInBlock = addedInBlock.tail
  }
}

class Interpreter(vocInit: Vocabulary) {
  /** unexpected error, typing error in input or expression does not simplify into value */
  case class Error(stack: List[Frame], msg: String) extends PError(msg)
  def fail(sf: SyntaxFragment, msg: String) = throw Error(stack, msg + ": " + sf)
  /** run-time error */
  case class RuntimeError(msg: String) extends PError(msg)
  private var voc = vocInit

  private var stack = List(Frame("toplevel", None, Nil))
  private def frame = stack.head
  private def push(f: Frame) {stack::=f}
  private def pop() {stack = stack.tail}

  def interpretDeclaration(d: Declaration) {
    voc = voc.append(d)
  }

  def interpretExpression(exp: Expression): Expression = {
    if (exp.interpreted) return exp
    val expI: Expression = exp match {
      case _: BaseValue => exp
      case _: BaseOperator => exp
      case SymbolRef(p) => voc.lookupPath(p) match {
        case Some(sd:SymDecl) => sd.value match {
          case None => exp // allow this?
          case Some(v) => interpretExpression(v)
        }
        case _ => fail(p, "not a value")
      }
      case VarRef(n) => frame.lookup(n) // frame values are always interpreted
      case VarDecl(n,_, vl, _) =>
        val vlI = vl match {
          case Some(v) => interpretExpression(v)
          case None => fail(exp, "uninitialized variable")
        }
        frame.add(n, vlI)
        UnitValue
      case Assign(t, v) =>
        val vI = interpretExpression(v)
        t match {
          case VarRef(n) => frame.update(n,vI)
          case _ => fail(exp,"complex target unsupported")
        }
        UnitValue
      case ExprOver(v,q) =>
        val qI = EvalInterpreter(q)(0)
        ExprOver(v,qI)
      case Structure(fs) =>
        val fsI = fs map {
          case sd: SymDecl => sd.copy(value = sd.value map interpretExpression)
        }
        Structure(fsI)
      case FieldRef(ow, n) =>
        val owI = interpretExpression(ow)
        owI match {
          case s: Structure =>
            val sd = s.lookup(n) match {
              case sd: SymDecl => sd
              case _ => fail(exp, "not an expression field")
            }
            if (sd.tp.isInstanceOf[FunType]) {
              // functions must be interpreted at call-time in the context of their owner
              FieldRef(owI,n)
            } else
              sd.value.get // exists by type-checking
          case _ => fail(exp,"owner not a structure")
        }
      case Block(es) =>
        frame.enterBlock
        var ret: Expression = UnitValue
        es.foreach {e =>
          ret = interpretExpression(e)
        }
        frame.leaveBlock
        ret
      case IfThenElse(c,t,eO) =>
        val cI = interpretExpression(c)
        cI match {
          case b: BoolValue => if (b.v) {
            interpretExpression(t)
          } else
            eO match {
              case Some(e) => interpretExpression(e)
              case None => UnitValue
            }
          case _ => fail(exp, "condition not a boolean")
        }
      case While(c,b) =>
        var break = false
        while (!break) {
          val cI = interpretExpression(c) match {
            case b: BoolValue => b.v
            case _ => fail(exp, "condition not a boolean")
          }
          if (cI) interpretExpression(b) else break = true
        }
        UnitValue
      case For(i, r, b) =>
        val rI = interpretExpression(r) match {
          case ListValue(vs) =>
            frame.enterBlock
            frame.add(i, UnitValue) // irrelevant value
            vs.foreach {v =>
              frame.update(i, v)
              interpretExpression(b)
            }
            frame.leaveBlock
            case _ => fail(exp, "range not a list")
        }
        UnitValue
      case lam: Lambda =>
        // lambdas must be interpreted at call-time, and the body is relative to the current frame
        lam.frame = frame
        lam
      case Application(f, as) =>
        val fI = interpretExpression(f)
        val asI = as map interpretExpression
        fI match {
          case o: BaseOperator =>
            applyOperator(o, asI)
          case lam: Lambda =>
            // is.decls.length == asI.length by type-checking
            // interpretation of lam has recorded the frame at abstraction time because
            // names in lam.body are relative to that
            val r = applyFunction(f.toString, None, lam, asI)
            r
          case FieldRef(ow, n) =>
            ow match {
              case str: Structure =>
                val fd = str.lookup(n) match {
                  case fd: SymDecl => fd
                  case _ => fail(exp, "not an expression")
                }
                fd.value.get match {
                  case lam: Lambda =>
                    applyFunction(n.toString, Some(str), lam, asI)
                  case _ => fail(f, "value of function field not a lambda")
                }
              case _ => fail(f, "owner of function not a structure")
            }
        }
      case Tuple(es) =>
        val esI = es map interpretExpression
        Tuple(esI)
      case Projection(t,i) =>
        val tI = interpretExpression(t)
        tI match {
          case Tuple(es) => es(i)
          case _ => fail(exp, "owner not a tuple")
        }
      case ListValue(es) =>
        val esI = es map interpretExpression
        ListValue(esI)
      case ListElem(l, i) =>
        val esI = interpretExpression(l) match {
          case ListValue(es) => es
          case _ => fail(exp, "owner not a list")
        }
        val iI = interpretExpression(i) match {
          case IntValue(n) => n
          case _ => fail(exp, "index not an integer")
        }
        if (iI < 0 || iI >= esI.length)
          throw RuntimeError("index out of bounds")
        esI(iI)
    } // end match
    expI.interpreted = true
    expI
  }

  def applyFunction(name: String, owner: Option[Structure], lam: Lambda, args: List[Expression]) = {
    val fes = (lam.ins.decls zip args) map {case (i,a) => FrameEntry(i.name,a)}
    push(Frame(name, owner, fes:::lam.frame.vars))
    val bI = interpretExpression(lam.body)
    pop()
    bI
  }

  def applyOperator(o: BaseOperator, as: List[Expression]): Expression = {
    o.operator match {
      case pf: PrefixOperator =>
        ((pf,as.head)) match {
          case (UMinus,(IntOrRatValue(x,y))) => IntOrRatValue(-x,y)
          case (Not,BoolValue(b)) => BoolValue(!b)
        }
      case inf: InfixOperator =>
        (inf,as(0),as(1)) match {
          case (Plus,IntOrRatValue(u,v),IntOrRatValue(x,y)) => IntOrRatValue(u * y + v * x,v * y)
          case (Minus,IntOrRatValue(u,v),IntOrRatValue(x,y)) => IntOrRatValue(u * y - v * x,v * y)
          case (Times,IntOrRatValue(u,v),IntOrRatValue(x,y)) => IntOrRatValue(u * x,v * y)
          case (Divide,IntOrRatValue(u,v),IntOrRatValue(x,y)) =>
            if (x == 0) throw RuntimeError("division by 0") else IntOrRatValue(u * y,v * x)
          case (c: Comparison,IntOrRatValue(u,v),IntOrRatValue(x,y)) =>
            val d = u * y - v * x
            val s = if (d > 0) 1 else if (d < 0) -1 else 0
            (s,c) match {
              case (-1,Less | LessEq) |
                   (1,Greater | GreaterEq) |
                   (0,LessEq | GreaterEq) => BoolValue(true)
              case _ => BoolValue(false)
            }
          case (c: Comparison,BoolValue(l),BoolValue(r)) =>
            val b = c match {
              case Less => !l && r
              case LessEq => !l || r
              case Greater => l && !r
              case GreaterEq => l || !r
            }
            BoolValue(b)
          case (And,BoolValue(l),BoolValue(r)) => BoolValue(l && r)
          case (Or,BoolValue(l),BoolValue(r)) => BoolValue(l || r)
          case (Plus,StringValue(l),StringValue(r)) => StringValue(l + r)
          case (Plus,ListValue(l),ListValue(r)) => ListValue(l ::: r)
          case (e: Equality,l: BaseValue,r: BaseValue) =>
            val b = ((e == Equal) == (l.value == r.value))
            BoolValue(b)
          case _ => fail(o, "no case for operator evaluation")
        }
    }
  }

  /** interpret the bodies of Eval, leave AST unchanged otherwise */
  object EvalInterpreter extends Traverser[Int] {
    override def apply(exp: Expression)(implicit i: Int) = exp match {
      case Eval(e) if i == 0 =>
        val eI = interpretExpression(e)
        eI match {
          case ExprOver(_,q) => q
          case _ => fail(eI, "evaluation result not an expression")
        }
      case _:Eval =>
        applyDefault(exp)(i-1)
      case _:ExprOver =>
        applyDefault(exp)(i+1)
      case _ => applyDefault(exp)
    }
  }
}
