package info.kwarc.p

import SyntaxFragment.matchC

case class MutableExpression(name: String, var value: Expression) {
  override def toString = name + " = " + value
}

trait MutableExpressionStore {
  private[p] def fields: List[MutableExpression]
  def getO(n: String) = fields.find(_.name == n)
  def get(n: String) = getO(n) match {
    case Some(f) => f.value
    case None => throw IError("variable does not exist: " + n)
  }
  def set(n: String, v: Expression) {
    fields.find(_.name == n).get.value = v
  }
}

/** @param name frame name, only used for error reporting
  * @param owner the [[Instance]] relative to which [[ClosedRef]]s are interpreted,
  *  e.g., empty if we are in an open module
  * @param fields the visible local variables
  *  e.g., the (immutable) arguments of the called functions, and mutable local declarations
  */
case class Frame(name: String, owner: Option[Instance], var fields: List[MutableExpression]) extends MutableExpressionStore {
  override def toString = name + ": " + owner + fields.mkString(", ")
  def allocate(n: String, vl: Expression) {
    fields ::= MutableExpression(n, vl)
    addedInBlock = (addedInBlock.head + 1) :: addedInBlock.tail
  }

  private var addedInBlock: List[Int] = Nil
  def enterBlock {
    addedInBlock ::= 0
  }
  def leaveBlock {
    fields = fields.drop(addedInBlock.head)
    addedInBlock = addedInBlock.tail
  }
}

class Interpreter(vocInit: Module) {
  private val debug = false
  /** unexpected error, e.g., typing error in input or expression does not simplify into value */
  case class Error(stack: List[Frame], msg: String) extends PError(msg)
  def fail(msg: String)(implicit sf: SyntaxFragment) = throw Error(stack, msg + ": " + sf)
  /** run-time error while processing well-formed input, e.g., index out of bounds */
  case class RuntimeError(msg: String) extends PError(msg)

  private var voc = vocInit

  private var stack = List(Frame("toplevel", None, Nil))
  private def frame = stack.head
  private def push(f: Frame) {stack::=f}
  private def pop() {stack = stack.tail}

  def interpretDeclaration(d: Declaration) {
    // TODO
    voc = voc.append(d)
  }

  def interpretExpressionInFrame(f: Frame, exp: Expression) = {
    push(f)
    val expI = interpretExpression(exp)
    pop()
    expI
  }
  def interpretExpression(exp: Expression): Expression = {
    if (debug) println("interpreting: " + exp)
    implicit val cause = exp
    exp match {
      case _: BaseValue => exp
      case _: BaseOperator => exp
      case ClosedRef(n) => frame.owner match {
        case None =>
          fail("no owner for closed references") //TODO allow this as an abstract declaration in a module; all elimination forms below must remain uninterpreted
        case Some(inst) =>
          inst.getO(n) match {
            case Some(me) => me.value
            case None => voc.lookupPath(inst.theory / n) match {
              case Some(d: ExprDecl) => d.dfO match {
                case Some(e) => e
                case None => fail("no definiens")
              }
              case _ => fail("not an expression")
            }
          }
      }
      case OpenRef(p, ownO) =>
        voc.lookupPath(p) match {
          case Some(sd:ExprDecl) => sd.dfO match {
            case None => fail("no definiens") //TODO allow this as an abstract declaration in a module; all elimination forms below must remain uninterpreted
            case Some(v) =>
              ownO match {
                case None =>
                  // current owner interprets all closed references
                  interpretExpression(v)
                case Some(own) =>
                  val ownI = interpretExpression(own) match {
                    case i: Instance => i
                    case _ => fail("not an instance")
                  }
                  val fr = Frame(p.toString,Some(ownI),Nil)
                  interpretExpressionInFrame(fr,v)
              }
          }
          case _ => fail("not an expression")
        }
      case VarRef(n) => frame.get(n) // frame values are always interpreted
      case VarDecl(n,_, vl, _) =>
        val vlI = vl match {
          case None => fail("uninitialized variable")
          case Some(v) => interpretExpression(v)
        }
        frame.allocate(n, vlI)
        UnitValue
      case Assign(t, v) =>
        val vI = interpretExpression(v)
        assign(t,vI)
        UnitValue
      case ExprOver(v,q) =>
        val qI = EvalInterpreter(q)(0)
        ExprOver(v,qI)
      case Eval(_) =>
        fail("eval outside quotation")
      case inst:Instance =>
        // if instance had already been created, this would not be reached
        val fsI = inst.decls.collect {
          case sd: ExprDecl =>
            val dfI = interpretExpression(sd.dfO.get)
            MutableExpression(sd.name, dfI)
        }
        val runtimeInst = inst.copy() // create new Java object for every new instance
        runtimeInst.fields = fsI.reverse
        // execute the inherited field initializers in the context of this instance
        // variables available in the scope surrounding 'inst' are not visible
        push(Frame("new instance", Some(runtimeInst), Nil))
        val mod = voc.lookupModule(runtimeInst.theory).getOrElse(fail("unknown module"))
        // TODO: i.dfO
        mod.decls.foreach {
          case sd: ExprDecl if sd.dfO.isDefined =>
            val d = sd.dfO.get
            val dI = interpretExpression(d)
            if (!(d eq dI)) { // or sd.mutable
              inst.fields ::= MutableExpression(sd.name, dI)
            }
          case _ =>
        }
        pop()
        runtimeInst
      case OwnedExpr(own, e) =>
        val ownI = interpretExpression(own)
        ownI match {
          case inst: Instance if inst.isRuntime =>
            val fr = Frame(e.toString, Some(inst), Nil)
            interpretExpressionInFrame(fr, e)
          case _ => fail("owner not a runtime instance")
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
          case _ => fail("condition not a boolean")
        }
      case While(c,b) =>
        var break = false
        while (!break) {
          val cI = interpretExpression(c) match {
            case b: BoolValue => b.v
            case _ => fail("condition not a boolean")
          }
          if (cI) interpretExpression(b) else break = true
        }
        UnitValue
      case For(i, r, b) =>
        val rI = interpretExpression(r)
        rI match {
          case ListValue(vs) =>
            frame.enterBlock
            frame.allocate(i, null) // irrelevant value
            vs.foreach {v =>
              frame.set(i, v)
              interpretExpression(b)
            }
            frame.leaveBlock
            case _ => fail("range not a list")
        }
        UnitValue
      case lam: Lambda =>
        // lambdas must be interpreted at call-time, and the body is relative to the current frame
        val lamC = lam.copy() // the same lambda can be interpreted in different frames
        lamC.frame = frame
        lamC
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
          case _ => fail("not a function")(f)
        }
      case Tuple(es) =>
        val esI = es map interpretExpression
        Tuple(esI)
      case Projection(t,i) =>
        val tI = interpretExpression(t)
        tI match {
          case Tuple(es) => es(i)
          case _ => fail("owner not a tuple")(tI)
        }
      case ListValue(es) =>
        val esI = es map interpretExpression
        ListValue(esI)
      case OptionValue(e) =>
        if (e == null) exp else OptionValue(interpretExpression(e))
      case ListElem(l, i) =>
        val esI = interpretExpression(l) match {
          case ListValue(es) => es
          case _ => fail("owner not a list")
        }
        val iI = interpretExpression(i) match {
          case IntValue(n) => n
          case _ => fail("index not an integer")
        }
        if (iI < 0 || iI >= esI.length)
          throw RuntimeError("index out of bounds")
        esI(iI)
    } // end match
  }

  private def assign(target: Expression, value: Expression): Unit = {
    (target,value) match {
      case (VarRef(""), _) => // ignore value
      case (VarRef(n),_) => frame.set(n,value)
      case (ClosedRef(n),_) => frame.owner match {
        case Some(inst) => inst.set(n, value)
        case None => fail("mutable field without owner")(target)
      }
      case (Tuple(es),Tuple(vs)) => (es zip vs).foreach {case (e,v) => assign(e,v)}
      case (ListValue(es), ListValue(vs)) =>
        if (es.length != vs.length) throw RuntimeError("lists have inequal length")
        (es zip vs).foreach {case (e,v) => assign(e,v)}
      case (Application(OpenRef(r,None), es), Application(OpenRef(s,None), vs)) if r == s =>
        (es zip vs) foreach {case (e,v) => assign(e,v)}
      case (eo:ExprOver, vo: ExprOver) =>
        val (es, eR) = EvalTraverser.replaceEvals(eo)
        val (vs, vR) = EvalTraverser.replaceEvals(vo)
        if (eR != vR) throw RuntimeError("shape of expressions does not match")
        (es.decls zip vs.decls) foreach {case (e,v) => assign(e.dfO.get, v.dfO.get)}
      case _ => fail("target unsupported")(target)
    }
  }

  def applyFunction(name: String, owner: Option[Instance], lam: Lambda, args: List[Expression]) = {
    val fes = (lam.ins.decls zip args) map {case (i,a) => MutableExpression(i.name,a)}
    val fr = Frame(name, owner, fes:::lam.frame.fields)
    interpretExpressionInFrame(fr, lam.body)
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
          case _ => fail("no case for operator evaluation")(o)
        }
    }
  }

  /** interpret the bodies of Eval, leave AST unchanged otherwise */
  object EvalInterpreter extends Traverser[Int] {
    override def apply(exp: Expression)(implicit i: Int) = matchC(exp) {
      case Eval(e) if i == 0 =>
        val eI = interpretExpression(e)
        eI match {
          case ExprOver(_,q) => q
          case _ => fail("evaluation result not an expression")(eI)
        }
      case _:Eval =>
        applyDefault(exp)(i-1)
      case _:ExprOver =>
        applyDefault(exp)(i+1)
      case _ => applyDefault(exp)
    }
  }
}
