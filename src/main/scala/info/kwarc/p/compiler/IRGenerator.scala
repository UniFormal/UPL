package info.kwarc.p.compiler

import info.kwarc.p.{Application, ApproxReal, BaseOperator, BoolValue, ClassType, ClosedRef, Declaration, Equality, ExprDecl, Expression, IfThenElse, Include, InfixOperator, Instance, KnownOperator, Minus, Module, NamedDeclaration, NumberType, NumberValue, OpenRef, Operator, OwnedExpr, Path, Plus, Program, PseudoOperator, Rat, RightAssociative, SymbolDeclaration, TheoryValue, Type}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object IRGenerator {
  def run(p: Program): IRProgram = {
    val ig = new IRGenerator(p.voc)

    p.voc.decls.foreach(d => ig.visitDeclaration(d, Path()))

    val (stmts, value) = ig.visitExpression(p.main)

    val main = IRFun("main", "i32", List(), stmts :+ IRReturn(value))

    IRProgram(
      ig.structs,
      ig.declaredFunctions,
      ig.functions :+ main
    )
  }
}

class IRGenerator(val voc: TheoryValue) {
  private val mallocFun = IRFun("malloc", "ptr", List("i64"), List())
  private val declaredFunctions: List[IRFun] = List(mallocFun)
  private var functions: List[IRFun] = List()
  private var globalFunctions: Map[Path, IRFun] = Map()
  private var structs: List[IRStruct] = List()
  private var nameCount: Map[String, Int] = Map().withDefaultValue(0)

  // Maps from named expression to vTable index for the method of that expression for each closed module
  private val methodLayout: mutable.Map[Path, mutable.Map[IRFun, Int]] = mutable.Map()

  def fresh(name: String): String = {
    val c = nameCount(name)
    nameCount = nameCount.updated(name, c + 1)
    s"$name$c"
  }

  private def visitDeclaration(d: Declaration, p: Path): Unit = d match {
    case Module(modName, closed, df) =>
      val modP = p / modName
      if (closed) {
        // class
        var fields: List[(String, String)] = List()
        val vtableName = s"${modP}_vtable"
        fields :+= ("__vtable__", s"%$vtableName*")
        var vTableFields: List[(String, String)] = List()
        var virtualMethodIndex = 0
        val virtualMethodIndice: mutable.Map[IRFun, Int] = mutable.Map()
        df.decls.foreach {
          case Include(OpenRef(p), dfO, realize) =>
            val vtableName = s"${p}_vtable"
            fields :+= ("__vtable__", s"%$vtableName*")
          case ExprDecl(name, tc, tp, dfO, ntO, modifiers) =>
            val stmts = dfO match {
              case Some(expression) =>
                val (stmts, value) = visitExpression(expression)
                stmts :+ IRReturn(value)
              case None => List(IRReturn(IRConstInt(0)))
            }
            // TODO ensure names are unique
            val fun = IRFun(s"$modP.$name", toLLVMType(tp), List(), stmts)
            virtualMethodIndice(fun) = virtualMethodIndex
            functions :+= fun
            vTableFields :+= ("__virtual_method__", "ptr")
            virtualMethodIndex += 1
          //            fields :+= (name, toLLVMType(tp))
        }
        val vTableStruct = IRStruct(vtableName, vTableFields)
        methodLayout(modP) = virtualMethodIndice
        structs :+= vTableStruct
        structs :+= IRStruct(modP.toString, fields)
      } else {
        df.decls.foreach(d => visitDeclaration(d, p/modName))
      }
    case ExprDecl(name, tc, tp, dfO, ntO, modifiers) =>
      val (stmts, retTp) = dfO match {
        case Some(expression) =>
          val (stmts, value) = visitExpression(expression)

          (stmts :+ IRReturn(value), value.llvmType())
        case None => (List(IRReturn(IRConstInt(0))), "i32")
      }

      val fun = IRFun(s"__global__${p / name}", retTp, List(), stmts)
      functions :+= fun
      globalFunctions = globalFunctions.updated(p / name, fun)
    case _ =>
      sys.error(s"Unsupported declaration ${d.getClass} $d")
  }

  private def visitExpression(e: Expression): (List[IRStmt], IROperand) = e match {
    case NumberValue(tp, re, im) =>
      re match {
        // TODO
        case ApproxReal(value) => (Nil, IRConstInt(value.toInt))
        case Rat(enu, deno) => (Nil, IRConstInt(enu.toInt / deno.toInt))
      }

    case BoolValue(b) =>
      (Nil, IRConstInt(if (b) 1 else 0))

    case Equality(positive, tp, a, b) =>
      val (sa, ea) = visitExpression(a)
      val (sb, eb) = visitExpression(b)

      val tmp = I32(fresh("v"))
      val cmp = IRCmp(tmp, if (positive) "eq" else "ne", ea, eb)

      val result = I32(fresh("v"))
      val zext = IRI1toI32(result, tmp)

      (sa ++ sb ++ List(cmp, zext), result)
    case Application(fun, args) => fun match {
      case bo: BaseOperator =>
        bo.operator match {
          case inf: InfixOperator =>
            if (args.isEmpty) {
              visitExpression(inf.neutral.get)
            } else if (args.length == 1) {
              visitExpression(args.head)
            } else {
              val combinedStmts = ArrayBuffer.empty[IRStmt]

              def operator(op1: IROperand, op2: IROperand): (IRStmt, IROperand) = {
                val result = I32(fresh("v"))
                bo.operator match {
                  case Plus => (IRAdd(result, op1, op2), result)
                  case Minus => (IRSub(result, op1, op2), result)
                }
              }

              // TODO Associativity
              // inf.assoc
              val (stmts, initial) = visitExpression(args.head)
              var tmp = initial
              combinedStmts ++= stmts

              args.tail.foreach { arg =>
                val (stmts, operand) = visitExpression(arg)
                combinedStmts ++= stmts
                val (opStmt, res) = operator(tmp, operand)
                combinedStmts += opStmt
                tmp = res
              }
              (combinedStmts.toList, tmp)
            }
          case _ => sys.error(s"Unsupported operator type ${bo.operator.getClass} ${bo.operator}")
        }
    }

    case IfThenElse(cond, thn, Some(els)) =>
      val (condS, ec) = visitExpression(cond)
      val tmp = I32(fresh("v"))

      val trncS = IRI32ToI1(tmp, ec)

      val thnLS = IRLabel(fresh("then"))
      val elsLS = IRLabel(fresh("else"))
      val endLS = IRLabel(fresh("end"))

      val brEndS = IRBranch(endLS)
      val cndBrS = IRCondBranch(tmp, thnLS, elsLS)

      val (thnS, thnO) = visitExpression(thn)
      val (elsS, elsO) = visitExpression(els)

      val result = I32(fresh("v"))

      val phi = IRPhi(result, List((thnO, thnLS), (elsO, elsLS)))

      (condS ++ List(trncS, cndBrS, thnLS) ++ thnS ++ List(brEndS, elsLS) ++ elsS ++ List(brEndS, endLS, phi), result)
    case OpenRef(path) =>
      // TODO use appropriate type
      val fun = globalFunctions(path)
      val result = toIRVar(fresh("v"), fun.ret)
      val call = IrCall(result, fun, List())
      (List(call), result)
    case OwnedExpr(owner @ OpenRef(p), ownerDom, ClosedRef(name)) =>
      // TODO
      val pType = determineType(voc.lookupPath(p).get)
      val (stmts, vTablePtr) = visitExpression(owner)
      val baseFun = functions.find(f => f.name == (pType/name).toString).get
      val vtableName = s"${pType}_vtable"
      val struct = structs.find(s => s.name == vtableName).get
      val idx = methodLayout(pType)(baseFun)
      val fieldPtr = IRVarPtr(fresh(s"ptr_${pType}_vtable_index${idx}_"))
      val getElement = IRGetElement(fieldPtr, struct, vTablePtr.asInstanceOf[IRVarPtr], idx)
      val funPtr = IRVarPtr(fresh(s"ptr_${pType}_fun"))

      val load = IRLoad(funPtr, fieldPtr)

      val result = toIRVar(fresh("v"), baseFun.ret)
      // The actual function invoked may be a different one, but we only care about parameter types and return type
      // which should be the same
      // TODO parameters
      val call = IrPtrCall(result, baseFun.ret, funPtr, List())

      (stmts ++ List(getElement, load, call), result)
    case Instance(theory) =>
      val size = I64(fresh("size"))

      // TODO better way to figure out instance type
      val p = theory.decls.head.asInstanceOf[Include].dom.asInstanceOf[OpenRef].path
      val vtableName = s"${p}_vtable"
      val struct = structs.find(s => s.name == vtableName).get
      val computeSize = IRComputeSize(size, struct)

      val vTablePtr = IRVarPtr(fresh(s"ptr_${p}_vtable_"))
      val malloc = IrCall(vTablePtr, mallocFun, List(size))

      // initialize vtable fields
      val initStmts = ArrayBuffer.empty[IRStmt]

      methodLayout(p).foreach { case (fun, idx) =>
        val fieldPtr = IRVarPtr(fresh(s"ptr_${p}_vtable_index${idx}_"))
        val getElement = IRGetElement(fieldPtr, struct, vTablePtr, idx)
        val store = IRStore(IRFunPtr(fun), fieldPtr)
        initStmts += getElement
        initStmts += store
      }

      (List(computeSize, malloc) ++ initStmts, vTablePtr)
    case _ =>
      sys.error(s"Unsupported expression ${e.getClass} $e")
  }

  private def toLLVMType(tp: Type): String = tp match {
    case nt: NumberType =>
      nt match {
        case NumberType.Nat => "i32"
        case NumberType.Int => "i32"
        case _ => sys.error(s"Unsupported number type ${nt.getClass} $nt")
      }
    case _ =>
      sys.error(s"Unsupported type ${tp.getClass} $tp")
  }

  private def toIRVar(name: String, tp: String): IRVar = {
    tp match {
      case "i32" => I32(name)
      case "i64" => I64(name)
      case "ptr" => IRVarPtr(name)
      case _ => ???
    }
  }

  private def determineType(decl: NamedDeclaration): Path = {
    decl match {
      case Module(name, closed, df) => ???
      case ExprDecl(name, tc, ClassType(domain), dfO, ntO, modifiers) =>
        domain.decls.find(d => true).get.asInstanceOf[Include].dom.asInstanceOf[OpenRef].path
    }
  }

}