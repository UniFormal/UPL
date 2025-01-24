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
  def set(n: String, v: Expression) = {
    fields.find(_.name == n).get.value = v
  }
}

case class LocalEnvironment(var fields: List[MutableExpression]) extends MutableExpressionStore

object LocalEnvironment {
  def empty = LocalEnvironment(Nil)
}

/** @param name frame name, only used for error reporting
  * @param region the [[Instance]] relative to which [[ClosedRef]]s are interpreted,
  *  e.g., empty if we are in an open module
  * @param local the visible local variables
  * @param transparent whether lookups may continue in the previous frame
  *  e.g., the (immutable) arguments of the called functions, and mutable local declarations
  */
case class RegionalEnvironment(name: String, region: Option[Instance] = None, local: LocalEnvironment = LocalEnvironment.empty, transparent: Boolean = false) {
  override def toString = name + ": " + region + fields.mkString(", ")
  def fields = local.fields
  def allocate(n: String, vl: Expression) = {
    local.fields ::= MutableExpression(n, vl)
    addedInBlock = (addedInBlock.head + 1) :: addedInBlock.tail
  }

  def inNewBlock[A](a: => A) = {
    addedInBlock ::= 0
    try {a}
    finally {
      local.fields = local.fields.drop(addedInBlock.head)
      addedInBlock = addedInBlock.tail
    }
  }
  private var addedInBlock: List[Int] = Nil
}

class GlobalEnvironment(var voc: Module) {
  var regions = List(RegionalEnvironment("toplevel", None, LocalEnvironment.empty, false))
  def frame = regions.head
  def inFrame[A](f: RegionalEnvironment)(a: => A) = {
    regions ::= f
    try {a}
    finally {regions = regions.tail}
  }

  def lookupLocalO(n: String): Option[Expression] = {
    var rs = regions
    while (rs.nonEmpty) {
      rs.head.local.getO(n) match {
        case Some(v) => return Some(v.value)
        case None =>
          if (rs.head.transparent) rs = rs.tail
          else rs = Nil
      }
    }
    None
  }

  def lookupRegional(n: String): Expression = {
    var rs = regions
    while (rs.nonEmpty) {
      rs.head.region match {
        case None =>
          throw IError("no instance")
        case Some(inst) =>
          // try in instance
          inst.getO(n) match {
            case Some(v) =>
              return v.value
            case None =>
              // try inherited theories
              GlobalContext(voc).push(inst.theory).lookupRegional(n) match {
                case Some(ed: ExprDecl) => return ed.dfO.get
                case Some(d) => throw IError("unexpected declaration")
                case None =>
                  // try surrounding frame
                  if (rs.head.transparent) rs = rs.tail
                  else rs = Nil
              }
          }
      }
    }
    throw IError("unknown field")
  }
}

// ********************************* interpretation

object Interpreter {
  def run(p: Program) = {
    val ip = new Interpreter(p.toModule)
    val r = ip.interpretExpression(p.main)
    (ip,r)
  }
}

class Interpreter(vocInit: Module) {
  private val debug = false
  /** unexpected error, e.g., typing error in input or expression does not simplify into value */
  case class Error(cause: SyntaxFragment, stack: List[RegionalEnvironment], msg: String) extends SError(cause.loc, msg)
  /** run-time error while processing well-formed input, e.g., index out of bounds */
  case class RuntimeError(cause: Expression, msg: String) extends SError(cause.loc, msg)
  def fail(msg: String)(implicit sf: SyntaxFragment) =
    throw Error(sf, stack, msg + ": " + sf)
  def abort(msg: String)(implicit sf: Expression) =
    throw RuntimeError(sf, msg + ": " + sf)

  private val env = new GlobalEnvironment(vocInit)
  def voc = env.voc
  private val globalContext = GlobalContext(voc)
  private def stack = env.regions
  private def frame = stack.head

  def interpretDeclaration(d: Declaration) = {
    d match {
      case ed: ExprDecl if ed.dfO.isDefined =>
        val df = ed.dfO.get
        val dfI = interpretExpression(df)
        val edI = ed.copy(dfO = Some(dfI))
        edI.global = true
        env.voc = env.voc.append(edI)
        edI
      case _ => fail("uninterpretable")(d)
    }
  }

  def interpretExpressionInFrame(f: RegionalEnvironment, exp: Expression) = {
    env.inFrame(f) {
      interpretExpression(exp)
    }
  }
  def interpretExpression(exp: Expression): Expression = {
    if (debug) println("interpreting: " + exp)
    implicit val cause = exp
    exp match {
      case _: BaseValue => exp
      case _: BaseOperator => exp
      case OpenRef(p) =>
        env.voc.lookupPath(p) match {
          case Some(sd: ExprDecl) => sd.dfO match {
            case None => fail("no definiens") //TODO allow this as an abstract declaration in a module; all elimination forms below must remain uninterpreted
            case Some(v) => interpretExpression(v) //TODO this re-evaluates the definiens
          }
          case _ => fail("not an expression")
        }
      case ClosedRef(n) => env.lookupRegional(n)
      case VarRef(n) =>
        env.lookupLocalO(n) match {
          case Some(d) => d // frame values are always interpreted
          case None => fail("undefined variable") // maybe allow later, e.g., when computing with quotations
        }
      case VarDecl(n,_,vl,_,_) =>
        val vlI = vl match {
          case None => fail("uninitialized variable")
          case Some(v) => interpretExpression(v)
        }
        frame.allocate(n,vlI)
        vlI
      case Assign(t,v) =>
        val vI = interpretExpression(v)
        assign(t,vI)(true, globalContext)
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
      case inst: Instance =>
        // instance creation
        val runtimeInst = inst.copy() // create new Java object for every new instance
        runtimeInst.fields = Nil
        val initDecls = inst.theory.decls
        val re = RegionalEnvironment("new instance",Some(runtimeInst), transparent = true)
        // execute all fields in the context of this instance
        case class InterpretationInput(decls: List[Declaration], from: Option[Include])
        var todo = List(InterpretationInput(initDecls, None))
        env.inFrame(re) {
          while (todo.nonEmpty) {
            val InterpretationInput(d :: ds, inclO) :: tail = todo
            todo = if (ds.isEmpty) tail else InterpretationInput(ds,inclO) :: tail
            d match {
              case _:Module => fail("unexpected module in instance")
              case _: TypeDecl => // not needed
              case sd: ExprDecl if runtimeInst.getO(sd.name).isDefined => // definition from elsewhere already executed
              case sd: ExprDecl =>
                val df = inclO match {
                  case None =>
                    sd.dfO.getOrElse(fail("no definiens"))
                  case Some(incl) =>
                    // execute inherited definition and then apply delegate
                    OwnedExpr(incl.dfO.get, incl.theory, sd.toRef)
                }
                val dfI = interpretExpression(df)
                // we keep all fields that are local (i.e., a constructor argument),
                // declared in parent and mutable, or inherited and immutable and not values
                // other fields can be looked up in the parent, in particular all lambdas
                // TODO: lambdas may require keeping the previous frame
                if (inclO.isEmpty || sd.mutable || !(df eq dfI)) {
                  runtimeInst.fields ::= MutableExpression(sd.name,dfI)
                }
              case incl: Include =>
                // execute inherited field initializers if necessary
                val delegateO = incl.dfO match {
                  case Some(df) =>
                    // execute and remember delegate
                    val dfI = interpretExpression(df)
                    Some(incl.copy(dfO = Some(dfI)))
                  case _ => None
                }
                // append at the end so that constructor fields are executed before inherited fields
                val mod = env.voc.lookupModule(incl.dom).getOrElse(fail("unknown module"))
                todo = todo ::: List(InterpretationInput(mod.decls, delegateO))
            }
          }
        }
        runtimeInst
      case OwnedExpr(own,_,e) =>
        val ownI = interpretExpression(own)
        ownI match {
          case inst: Instance if inst.isRuntime =>
            val fr = RegionalEnvironment(e.toString,Some(inst))
            interpretExpressionInFrame(fr,e)
          case _ => fail("owner not a runtime instance")
        }
      case Block(es) =>
        frame.inNewBlock {
          var ret: Expression = UnitValue
          es.foreach {e =>
            ret = interpretExpression(e)
          }
          ret
        }
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
      case For(vd,r,b) =>
        val rI = interpretExpression(r)
        rI match {
          case CollectionValue(vs) =>
            frame.inNewBlock {
              frame.allocate(vd.name,null) // irrelevant value
              val vsI = vs.map {v =>
                frame.local.set(vd.name,v)
                interpretExpression(b)
              }
              CollectionValue(vsI)
            }
          case _ => fail("range not a list")
        }
      case Return(e,thrw) =>
        val eI = interpretExpression(e)
        throw ReturnFound(eI,thrw)
      case Match(e,cases,handle) =>
        // cases must be run if (i) this is a match, or (ii) this is a catch and e threw an exception
        val (eI,runCases) = try {
          (interpretExpression(e),!handle)
        } catch {
          case ReturnFound(exc,true) if handle =>
            (exc,true)
        }
        def doCases(mcs: List[MatchCase]): Expression = mcs match {
          case Nil =>
            if (handle) throw ReturnFound(eI,true) // bubble up exception
            else fail("match error: " + eI)
          case mc :: rest =>
            val mcI = frame.inNewBlock {
              mc.context.decls foreach {vd => frame.allocate(vd.name,null)}
              val matched = assign(mc.pattern,eI)(false, globalContext)
              if (matched) {
                mc.context.decls.foreach {vd =>
                  if (frame.local.get(vd.name) == null)
                    fail("expression matched but undefined variables remain")
                }
                Some(interpretExpression(mc.body))
              } else {
                None
              }
            }
            mcI getOrElse {
              doCases(rest)
            }
        }
        if (runCases) doCases(cases) else eI
      case _:MatchCase => fail("match case outside match")
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
            try {Operator.simplify(o.operator, asI)}
            catch {case ASTError(m) =>
              fail(m)
            }
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
          abort("index out of bounds")
        }
        val n = if (iI < 0) iI + len else iI
        esI(n.toInt)
      case Quantifier(q, ctx, bd) =>
        val vds = ctx.variables
        val its = vds.map {vd => makeIterator(vd.tp)}
        frame.inNewBlock {
          vds.foreach {vd => frame.allocate(vd.name,null)} // initial value irrelevant
          val it = Enumeration.product(its)
          it.take(100).foreach {es =>
            (vds zip es).foreach {case (v,e) => frame.local.set(v.name,e)}
            val bdI = interpretExpression(bd)
            if (bdI == BoolValue(!q)) return bdI
          }
        }
        BoolValue(q) // only correct if we've tried all values
      case Assert(f) =>
        val fI = interpretExpression(f)
        fI match {
          case BoolValue(true) =>
          case BoolValue(false) => abort("assertion failed: " + f)
          case _ => abort("assertion inconclusive: " + f)
        }
        UnitValue
    } // end match
  }

  private object TypeInterpreter extends StatelessTraverser {
    override def apply(e: Expression)(implicit gc:GlobalContext, a: Unit) = interpretExpression(e)
  }

  private def makeIterator(tp: Type): Iterator[Expression] = {
    val tpN = new Checker(ErrorThrower).typeNormalize(GlobalContext(env.voc), tp)
    val tpI = TypeInterpreter(tpN)(null,())
    tpI match {
      case EmptyType => Iterator.empty
      case UnitType => Iterator(UnitValue)
      case BoolType => Iterator(BoolValue(true), BoolValue(false))
      case IntType => Enumeration.Integers.map(i => IntValue(i))
      case RatType =>
        val it = new ProductIterator(Enumeration.Integers, Enumeration.Naturals)
        it.filter {case (i,n) => n != 0 && i.gcd(n) == 1}.map {case (i,n) => RatValue(i,n)}
      case p:ProdType if p.simple => Enumeration.product(p.simpleComps map makeIterator).map(es => Tuple(es))
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
          def next() = {val n = current; current += step; IntValue(n)}
        }
      case _ => fail("cannot iterate")(tp)
    }
  }

  /** called if assign fails */
  private def assignFail(msg: String)(implicit mustMatch: Boolean, cause: Expression) = {
    if (mustMatch) abort(msg)
    else false
  }
  private def assign(target: Expression, value: Expression)(implicit mustMatch: Boolean, gc: GlobalContext): Boolean = {
    implicit val cause = target
    val inQuote = gc.regions.length > 1
    (target,value) match {
      case (VarRef(""), _) =>
        true // ignore value
      case (VarRef(n),v) =>
        if (inQuote) {
          VarRef(n) == v
        } else if (mustMatch || frame.local.get(n) == null) {
          // assignment to n, or n is pattern-variable
          frame.local.set(n,value)
          true
        } else {
          // variable reference in (possibly non-linear) pattern
          frame.local.get(n) == v
        }
      case (vd: VarDecl, v) if !inQuote =>
        frame.allocate(vd.name, v)
        true
      case (r: Ref, s) if inQuote =>
        r == s
      case (ClosedRef(n),_) if !inQuote => frame.region match {
        case Some(inst) =>
          if (mustMatch) {
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
        // TODO depends on type
        if (es.length != vs.length) {
          assignFail("collections have inequal length")
        } else {
          (es zip vs).forall {case (e,v) => assign(e,v)}
        }
      case (Application(r: Ref, es), Application(s: Ref, vs)) if r == s =>
        (es zip vs) forall {case (e,v) => assign(e,v)}
      case (Application(BaseOperator(op,_),args), r) =>
        val argsE = Operator.invert(op,r).getOrElse {
          fail("operator cannot be inverted")(target)
        }
        if (argsE.length != args.length) fail("wrong number of arguments")(target)
        (args zip argsE).forall {case (a,e) => assign(a,e)}
      case (Lambda(ei,eb), Lambda(vi,vb)) if inQuote =>
        // contexts must match up to alpha if types are equal
        val ren = BiContext(ei,vi).renameLeftToRight
        assign(eb substitute ren, vb)(mustMatch, gc.append(vi))
      case (Quantifier(eq,ei,eb), Quantifier(vq,vi,vb)) if inQuote =>
        // TODO: allow alpha renaming
        if (eq != vq || ei != vi)
          assignFail("inequal terms")
        else {
          val ren = BiContext(ei,vi).renameLeftToRight
          assign(eb substitute ren,vb)(mustMatch,gc.append(vi))
        }
      case (eo:ExprOver, vo: ExprOver) =>
        assign(eo.expr, vo.expr)(mustMatch, gc.push(vo.scope))
      case (Eval(t), Eval(v)) =>
        assign(t,v)(mustMatch, gc.pop())
      case (Eval(t), v) if inQuote =>
        assign(t, ExprOver(gc.theory, v))(mustMatch, gc.pop())
        /*val (es, eR) = EvalTraverser.replaceEvals(eo)
        val (vs, vR) = EvalTraverser.replaceEvals(vo)
        if (eR != vR) {
          assignFail("shape of expressions does not match")
        } else {
          (es.decls zip vs.decls) forall {case (e,v) => assign(e.dfO.get,v.dfO.get)}
        }*/
      case (t,v) =>
        if (t == v) true
        else assignFail("pattern unsupported: " + t)
    }
  }

  def applyFunction(name: String, owner: Option[Instance], lam: Lambda, args: List[Expression]) = {
    val fes = (lam.ins.decls.reverse zip args) map {case (i,a) => MutableExpression(i.name,a)}
    val fr = RegionalEnvironment(name, owner, LocalEnvironment(fes:::lam.frame.fields), false)
    interpretExpressionInFrame(fr, lam.body)
  }

  /** interpret the bodies of Eval, leave AST unchanged otherwise */
  object EvalInterpreter extends StatelessTraverser {
    override def apply(exp: Expression)(implicit gc: GlobalContext, a: Unit) = matchC(exp) {
      case Eval(e) if gc.regions.length == 2 => // always called with 2 regions: default + the scope of the quoted expression
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
  def next() = {
    if (!current.hasNext) {
      if (nextFromA && aI.hasNext) {
        val a = aI.next()
        as ::= a
        current = bs.iterator.map(b => (a,b))
        if (bI.hasNext) nextFromA = false
      } else if (bI.hasNext) {
        val b = bI.next()
        bs ::= b
        current = as.iterator.map(a => (a,b))
        if (aI.hasNext) nextFromA = true
      }
    }
    current.next()
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
    def next() = {
      current += 1;
      current
    }
  }
  val Integers: Iterator[BigInt] = Iterator(BigInt(0)) ++ Naturals.flatMap(n => Iterator(n,-n))
}