package info.kwarc.p

import SyntaxFragment.matchC

// ****************************** environments

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

case class LocalEnvironment(var fields: List[MutableExpression]) extends MutableExpressionStore

object LocalEnvironment {
  def empty = LocalEnvironment(Nil)
}

/** @param name frame name, only used for error reporting
  * @param owner the [[Instance]] relative to which [[ClosedRef]]s are interpreted,
  *  e.g., empty if we are in an open module
  * @param fields the visible local variables
  *  e.g., the (immutable) arguments of the called functions, and mutable local declarations
  */
case class RegionalEnvironment(name: String, region: Option[Instance], local: LocalEnvironment) {
  override def toString = name + ": " + region + fields.mkString(", ")
  def fields = local.fields
  def allocate(n: String, vl: Expression) {
    local.fields ::= MutableExpression(n, vl)
    addedInBlock = (addedInBlock.head + 1) :: addedInBlock.tail
  }

  private var addedInBlock: List[Int] = Nil
  def enterBlock {
    addedInBlock ::= 0
  }
  def leaveBlock {
    local.fields = local.fields.drop(addedInBlock.head)
    addedInBlock = addedInBlock.tail
  }
}

object RegionalEnvironment {
  def apply(name: String, reg: Option[Instance] = None): RegionalEnvironment = RegionalEnvironment(name, reg, LocalEnvironment.empty)
}

class GlobalEnvironment(var voc: Module) {
  var regions = List(RegionalEnvironment("toplevel", None, LocalEnvironment.empty))
  def frame = regions.head
  def push(f: RegionalEnvironment) {regions::=f}
  def pop() {regions = regions.tail}
}

// ********************************* interpretation

class Interpreter(vocInit: Module) {
  private val debug = false
  /** unexpected error, e.g., typing error in input or expression does not simplify into value */
  case class Error(stack: List[RegionalEnvironment], msg: String) extends PError(msg)
  def fail(msg: String)(implicit sf: SyntaxFragment) = throw Error(stack, msg + ": " + sf)
  /** run-time error while processing well-formed input, e.g., index out of bounds */
  case class RuntimeError(msg: String) extends PError(msg)

  private val env = new GlobalEnvironment(vocInit)
  private def stack = env.regions
  private def frame = stack.head

  def interpretDeclaration(d: Declaration) {
    // TODO
    env.voc = env.voc.append(d)
  }

  def interpretExpressionInFrame(f: RegionalEnvironment, exp: Expression) = {
    env.push(f)
    val expI = interpretExpression(exp)
    env.pop()
    expI
  }
  def interpretExpression(exp: Expression): Expression = {
    if (debug) println("interpreting: " + exp)
    implicit val cause = exp
    exp match {
      case _: BaseValue => exp
      case _: BaseOperator => exp
      case ClosedRef(n) => frame.region match {
        case None =>
          fail("no owner for closed references") //TODO allow this as an abstract declaration in a module; all elimination forms below must remain uninterpreted
        case Some(inst) =>
          inst.getO(n) match {
            case Some(me) => me.value
            case None =>
              val ExtendedTheory(instD,_) = inst.theory
              env.voc.lookupPath(instD / n) match {
              case Some(d: ExprDecl) => d.dfO match {
                case Some(e) => e
                case None => fail("no definiens")
              }
              case _ => fail("not an expression")
            }
          }
      }
      case OpenRef(p) =>
        env.voc.lookupPath(p) match {
          case Some(sd:ExprDecl) => sd.dfO match {
            case None => fail("no definiens") //TODO allow this as an abstract declaration in a module; all elimination forms below must remain uninterpreted
            case Some(v) => interpretExpression(v)
          }
          case _ => fail("not an expression")
        }
      case VarRef(n) => frame.local.get(n) // frame values are always interpreted
      case VarDecl(n,_, vl, _, _) =>
        val vlI = vl match {
          case None => fail("uninitialized variable")
          case Some(v) => interpretExpression(v)
        }
        frame.allocate(n, vlI)
        UnitValue
      case Assign(t, v) =>
        val vI = interpretExpression(v)
        assign(t,vI)(true)
        UnitValue
      case ExprOver(v,q) =>
        val gc = GlobalContext("").push(v)
        val qI = EvalInterpreter(q)(gc,())
        ExprOver(v,qI)
      case Eval(_) =>
        fail("eval outside quotation")
      case inst: Instance if inst.isRuntime =>
        // instance reference
        inst
      case inst:Instance =>
        // instance creation
        val runtimeInst = inst.copy() // create new Java object for every new instance
        val initDecls = inst.theory.decls
        // TODO: replace all references to the current frame in initDecls with their current values
        // otherwise, we would have to keep those frames around; including in lambdas
        val initDeclsAbsolute = initDecls
        val re = RegionalEnvironment("new instance", Some(runtimeInst))
        env.push(re)
        // execute the constructor arguments in the context of this instance
        initDeclsAbsolute.foreach {
          case sd: ExprDecl =>
            val dfI = interpretExpression(sd.dfO.get)
            runtimeInst.fields ::= MutableExpression(sd.name, dfI)
          case _ =>
        }
        // execute inherited field initializers
        val instDom = inst.theory match {
          case PhysicalTheory(p) => p
          case _ => fail("non-atomic instance")
        }
        val mod = env.voc.lookupModule(instDom).getOrElse(fail("unknown module"))
        // TODO: i.dfO
        mod.decls.foreach {
          case sd: ExprDecl if sd.dfO.isDefined =>
            val d = sd.dfO.get
            val dI = interpretExpression(d)
            if (!(d eq dI) || sd.mutable) {
              runtimeInst.fields ::= MutableExpression(sd.name, dI)
            }
          case _ =>
        }
        env.pop()
        runtimeInst
      case OwnedExpr(own, e) =>
        val ownI = interpretExpression(own)
        ownI match {
          case inst: Instance if inst.isRuntime =>
            val fr = RegionalEnvironment(e.toString, Some(inst))
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
      case For(vd, r, b) =>
        val rI = interpretExpression(r)
        rI match {
          case CollectionValue(vs) =>
            frame.enterBlock
            frame.allocate(vd.name, null) // irrelevant value
            val vsI = vs.map {v =>
              frame.local.set(vd.name, v)
              interpretExpression(b)
            }
            frame.leaveBlock
            CollectionValue(vsI)
            case _ => fail("range not a list")
        }
      case Return(e, thrw) =>
        val eI = interpretExpression(e)
        throw ReturnFound(eI, thrw)
      case Match(e,cases, handle) =>
        val (eI,runCases) = try {
          (interpretExpression(e), !handle)
        } catch {
          case ReturnFound(exc, true) if handle =>
            (exc, true)
        }
        def doCases(mcs: List[MatchCase]): Expression = mcs match {
          case Nil => fail("match error")
          case mc::rest =>
            frame.enterBlock
            mc.context.decls foreach {vd => frame.allocate(vd.name,null)}
            val matched = assign(mc.pattern,eI)(false)
            if (matched) {
              mc.context.decls.foreach {vd =>
                if (frame.local.get(vd.name) == null)
                  throw fail("expression matched but undefined variables remain")
              }
              interpretExpression(mc.body)
            } else {
              frame.leaveBlock
              doCases(rest)
            }
          }
        if (runCases) doCases(cases) else eI
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
            Operator.simplify(o.operator, asI)
          case lam: Lambda =>
            // interpretation of lam has recorded the frame at abstraction time because
            // names in lam.body are relative to that
            val namedFunction = f match {
              case _:OpenRef | _:ClosedRef | _:VarRef => true
              case _ => false
            }
            val r = try {
              applyFunction(f.toString, None, lam, asI)
            } catch {
              case ReturnFound(e, false) if namedFunction => e
            }
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
      case CollectionValue(es) =>
        val esI = es map interpretExpression
        CollectionValue(esI)
      case ListElem(l, i) =>
        val esI = interpretExpression(l) match {
          case CollectionValue(es) => es
          case _ => fail("owner not a list")
        }
        val iI = interpretExpression(i) match {
          case IntValue(n) => n
          case _ => fail("index not an integer")
        }
        val len = esI.length
        if (iI < -len || iI >= len) {
          throw RuntimeError("index out of bounds")
        }
        val n = if (iI < 0) iI + len else iI
        esI(n.toInt)
      case Quantifier(q, ctx, bd) =>
        val vds = ctx.variables
        val its = vds.map {vd => makeIterator(vd.tp)}
        vds.foreach {vd => frame.allocate(vd.name, null)} // initial value irrelevant
        val it = Enumeration.product(its)
        it.take(100).foreach {es =>
          (vds zip es).foreach {case (v,e) => frame.local.set(v.name,e)}
          val bdI = interpretExpression(bd)
          if (bdI == BoolValue(!q)) return bdI
        }
        BoolValue(q) // only correct if we've tried all values
    } // end match
  }

  private object TypeInterpreter extends StatelessTraverser {
    override def apply(e: Expression)(implicit gc:GlobalContext, a: Unit) = interpretExpression(e)
  }

  private def makeIterator(tp: Type): Iterator[Expression] = {
    val tpN = Checker.typeNormalize(GlobalContext(env.voc), tp)
    val tpI = TypeInterpreter(tpN)(null,())
    tpI match {
      case EmptyType => Iterator.empty
      case UnitType => Iterator(UnitValue)
      case BoolType => Iterator(BoolValue(true), BoolValue(false))
      case IntType => Enumeration.Integers.map(i => IntValue(i))
      case RatType =>
        val it = new ProductIterator(Enumeration.Integers, Enumeration.Naturals)
        it.filter {case (i,n) => n != 0 && i.gcd(n) == 1}.map {case (i,n) => RatValue(i,n)}
      case ProdType(ts) => Enumeration.product(ts map makeIterator).map(es => Tuple(es))
      case CollectionKind.Option(t) => Iterator(CollectionValue(Nil)) ++ makeIterator(t)
      case CollectionType(t,k) => Enumeration.Naturals flatMap {n =>
        def idemp(es: List[Expression]) = es.distinct.length == es.length // repetition-normal, i.e., no repetitions
        def comm(es: List[Expression]) = es.sortBy(_.hashCode()) == es // order-normal, e.g., ordered by hashcode
        var it = makeIterator(t.power(n.toInt)).map(e => e.asInstanceOf[Tuple].comps)
        if (k.idemp) it = it.filter(idemp)
        if (k.comm) it = it.filter(comm)
        it.map(l => CollectionValue(l))
      }
      case iv: IntervalType if iv.concrete =>
        val (begin,end,step) = (iv.lower,iv.upper) match {
          case (Some(IntValue(i)),Some(IntValue(j))) => (i,Some(j),1)
          case (Some(IntValue(i)),None) => (i,None,1)
          case (None,Some(IntValue(j))) => (j,None,-1)
          case (None,None) => return Iterator.empty
          case _ => throw IError("impossible")
        }
        new Iterator[Expression] {
          var current = begin
          def hasNext = end.isEmpty || current <= end.get
          def next = {val n = current; current += step; IntValue(n)}
        }
      case _ => fail("cannot iterate")(tp)
    }
  }

  /** called if assign fails */
  private def assignFail(msg: String)(implicit failOnMismatch: Boolean) = {
    if (failOnMismatch) throw RuntimeError(msg)
    else false
  }
  private def assign(target: Expression, value: Expression)(implicit failOnMismatch: Boolean): Boolean = {
    (target,value) match {
      case (VarRef(""), _) =>
        true // ignore value
      case (VarRef(n),_) =>
        frame.local.set(n,value)
        true
      case (ClosedRef(n),_) => frame.region match {
        case Some(inst) =>
          if (failOnMismatch) {
            // force equality by changing current value
            inst.set(n, value)
            true
          } else {
            // compare against current value
            inst.get(n) == value
          }
        case None =>
          fail("mutable field without owner")(target)
      }
      case (Tuple(es),Tuple(vs)) => (es zip vs).forall {case (e,v) => assign(e,v)}
      case (CollectionValue(es), CollectionValue(vs)) =>
        if (es.length != vs.length) {
          assignFail("collections have inequal length")
        } else {
          (es zip vs).forall {case (e,v) => assign(e,v)}
        }
      case (Application(OpenRef(r), es), Application(OpenRef(s), vs)) if r == s =>
        (es zip vs) forall {case (e,v) => assign(e,v)}
      case (Application(BaseOperator(op,_),args), r) =>
        val argsE = Operator.invert(op,r).getOrElse {
          fail("operator cannot be inverted")(target)
        }
        if (argsE.length != args.length) fail("wrong number of arguments")(target)
        (args zip argsE).forall {case (a,e) => assign(a,e)}
      case (eo:ExprOver, vo: ExprOver) =>
        val (es, eR) = EvalTraverser.replaceEvals(eo)
        val (vs, vR) = EvalTraverser.replaceEvals(vo)
        if (eR != vR) {
          assignFail("shape of expressions does not match")
        } else {
          (es.decls zip vs.decls) forall {case (e,v) => assign(e.dfO.get,v.dfO.get)}
        }
      case (t,v) =>
        if (t == v) true
        else assignFail("pattern unsupported")
    }
  }

  def applyFunction(name: String, owner: Option[Instance], lam: Lambda, args: List[Expression]) = {
    val fes = (lam.ins.decls zip args) map {case (i,a) => MutableExpression(i.name,a)}
    val fr = RegionalEnvironment(name, owner, LocalEnvironment(fes:::lam.frame.fields))
    interpretExpressionInFrame(fr, lam.body)
  }

  /** interpret the bodies of Eval, leave AST unchanged otherwise */
  object EvalInterpreter extends StatelessTraverser {
    override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = matchC(exp) {
      case Eval(e) if gc.inPhysicalTheory =>
        val eI = interpretExpression(e)
        eI match {
          case ExprOver(_,q) => q
          case _ => fail("evaluation result not an expression")(eI)
        }
      case _ => applyDefault(exp)
    }
  }
}

case class ReturnFound(e: Expression, thrw: Boolean) extends Throwable

/** iterates over all pairs of values from two iterators
  * order: (a1,b1), (a2,b1), (b2,a2), (b2, a1), (a3,b2), (a3,b1), ...
  */

class ProductIterator[A,B](aI: Iterator[A], bI: Iterator[B]) extends Iterator[(A,B)] {
  private var as: List[A] = Nil
  private var bs: List[B] = Nil
  private var current: Iterator[(A,B)] = Iterator.empty
  private var nextFromA = true
  def hasNext = current.hasNext || aI.hasNext || bI.hasNext
  def next = {
    if (!current.hasNext) {
      if (nextFromA && aI.hasNext) {
        val a = aI.next
        as ::= a
        current = bs.iterator.map(b => (a,b))
        if (bI.hasNext) nextFromA = false
      } else if (bI.hasNext) {
        val b = bI.next
        bs ::= b
        current = as.iterator.map(a => (a,b))
        if (aI.hasNext) nextFromA = true
      }
    }
    current.next
  }
}

object Enumeration {
  def product(its: List[Iterator[Expression]]): Iterator[List[Expression]] = {
    if (its.isEmpty) Iterator.empty
    else {
      its.init.foldRight(its.last.map(x => List(x))) {case (next,sofar) =>
        new ProductIterator(next,sofar).map {case (x,l) => x :: l}
      }
    }
  }

  object Naturals extends Iterator[BigInt] {
    private var current = -1
    def hasNext = true
    def next = {
      current += 1;
      current
    }
  }
  val Integers: Iterator[BigInt] = Iterator(BigInt(0)) ++ Naturals.flatMap(n => Iterator(n,-n))
}