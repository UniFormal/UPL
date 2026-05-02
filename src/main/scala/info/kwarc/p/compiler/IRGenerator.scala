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

  private val closedModules: mutable.Map[Path, ClosedModule] = mutable.Map()

  private case class ClosedModule(
                                   struct: IRStruct,
                                   parentLayout: Map[Path, Int],
                                   fieldLayout: Map[String, Int],
                                   fieldLookup: Map[String, Path],
                                   field2Expression: Map[String, Expression]
                                 )

  def fresh(name: String): String = {
    val c = nameCount(name)
    nameCount = nameCount.updated(name, c + 1)
    s"${name}_$c"
  }

  private def visitDeclaration(d: Declaration, path: Path): Unit = d match {
    case Module(name, closed, df) =>
      val modulePath = path / name
      if (closed) {
        val fields = ArrayBuffer.empty[(String, String)]

        var fieldIndex = 0

        val parentLayout: mutable.Map[Path, Int] = mutable.Map()
        val fieldLayout: mutable.Map[String, Int] = mutable.Map()
        val fieldLookup: mutable.Map[String, Path] = mutable.Map()
        val field2Expression: mutable.Map[String, Expression] = mutable.Map()

        val includedFields: mutable.Set[String] = mutable.Set()
        val declaredFields: mutable.Set[String] = mutable.Set()
        df.decls.foreach {
          case Include(OpenRef(includePath), dfO, realize) =>
            closedModules(includePath).fieldLayout.foreach { case (field, idx) =>
              if (!includedFields.contains(field)) {
                fieldLookup(field) = includePath
              }
              includedFields += field
            }
            closedModules(includePath).field2Expression.foreach { case (field, function) =>
              declaredFields += field
            }
            val field = (includePath.toString, "ptr")

            fields += field
            parentLayout(includePath) = fieldIndex
            fieldIndex += 1

          case ExprDecl(name, tc, tp, dfO, ntO, modifiers) =>
            if (!includedFields.contains(name)) {
              val field = (name, "i32")
              fields += field
              fieldLayout(name) = fieldIndex
              fieldLookup(name) = modulePath
              fieldIndex += 1
            }
            if (!declaredFields.contains(name)) {
              dfO match {
                case Some(expression) =>
                  field2Expression(name) = expression
                case _ =>
              }
            }
        }

        val struct = IRStruct(modulePath.toString, fields.toList)
        closedModules(modulePath) = ClosedModule(struct, parentLayout.toMap, fieldLayout.toMap, fieldLookup.toMap, field2Expression.toMap)
        structs :+= struct
      } else {
        df.decls.foreach(d => visitDeclaration(d, path/name))
      }
    case ExprDecl(name, tc, tp, dfO, ntO, modifiers) =>
      val (stmts, retTp) = dfO match {
        case Some(expression) =>
          val (stmts, value) = visitExpression(expression)

          (stmts :+ IRReturn(value), value.llvmType())
        case None => (List(IRReturn(IRConstInt(0))), "i32")
      }

      val fun = IRFun(s"__global__${path / name}", retTp, List(), stmts)
      functions :+= fun
      globalFunctions = globalFunctions.updated(path / name, fun)
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
    case OwnedExpr(owner @ OpenRef(path), ownerDom, ClosedRef(name)) =>
      // TODO improve type detection
      val tp = determineType(voc.lookupPath(path).get)

      val closedModule = closedModules(tp)

      val combinedStmts = ArrayBuffer.empty[IRStmt]
      val (stmts, op) = visitExpression(owner)
      combinedStmts ++= stmts

      val modulePtr = op.asInstanceOf[IRVarPtr]

      // TODO better name
      val fieldPtr = IRVarPtr(fresh("ptr_field_index"))

      if (!closedModule.fieldLayout.contains(name)) {
        // Module which includes our field
        val parent = closedModule.fieldLookup(name)

        val parentIndex = closedModule.parentLayout(parent)
        val parentPtrPtr = IRVarPtr(fresh(s"ptr_ptr_$parent"))
        val getParentElement = IRGetElement(parentPtrPtr, closedModule.struct, modulePtr, parentIndex)
        combinedStmts += getParentElement

        val parentPtr = IRVarPtr(fresh(s"ptr_$parent"))

        val load = IRLoad(parentPtr, parentPtrPtr)
        combinedStmts += load

        val parentModule = closedModules(parent)
        val getFieldPtr = IRGetElement(fieldPtr, parentModule.struct, parentPtr, parentModule.fieldLayout(name))
        combinedStmts += getFieldPtr
      } else {
        val getFieldPtr = IRGetElement(fieldPtr, closedModule.struct, modulePtr, closedModule.fieldLayout(name))
        combinedStmts += getFieldPtr

      }

      val result = I32(fresh("v"))
      val load = IRLoad(result, fieldPtr)
      combinedStmts += load

      (combinedStmts.toList, result)
    case Instance(theory) =>
      // TODO better way to figure out instance type
      val path = theory.decls.head.asInstanceOf[Include].dom.asInstanceOf[OpenRef].path

      val closedModule = closedModules(path)
      val parentModules = closedModule.parentLayout.map { case (parent, _) =>
        (parent, allocClosedModuleStruct(closedModules(parent)))
      }
      val (stmts, ptr) = allocClosedModuleStruct(closedModule)

      var moduleStructs: Map[Path, IRVarPtr] = parentModules.map{ case (path, (_, ptr)) => (path, ptr) }
      moduleStructs = moduleStructs.updated(path, ptr)

      val combinedStmts = ArrayBuffer.empty[IRStmt]
      combinedStmts ++=  parentModules.flatMap(m => m._2._1)
      combinedStmts ++= stmts

      var assignments: Map[String, (List[IRStmt], IROperand)] = Map()
      // Default theory declarations
      moduleStructs.foreach { case (path, _) =>
        closedModules(path).field2Expression.foreach { case (field, expression) =>
          assignments = assignments.updated(field, visitExpression(expression))
        }
      }
      // Instance assignments
      theory.decls.foreach {
        case ExprDecl(name, _, _, Some(expression), _, _) =>
          assignments = assignments.updated(name, visitExpression(expression))
        case _ =>
      }
      combinedStmts += IRComment("Assign fields")
      assignments.foreach { case (name, (stmts, operand)) =>
        val module = closedModule.fieldLookup(name)
        val structPtr = moduleStructs(module)
        combinedStmts ++= stmts
        combinedStmts ++= assignField(module, structPtr, closedModules(module).fieldLayout(name), operand)
      }

      // Assign parent pointers
      combinedStmts += IRComment("Assign parent pointers")
      moduleStructs.foreach { case (path, structPtr) =>
        closedModules(path).parentLayout.foreach { case (parent, index) =>
          combinedStmts ++= assignField(path, structPtr, index, moduleStructs(parent))
        }
      }

      (combinedStmts.toList, ptr)
    case _ =>
      sys.error(s"Unsupported expression ${e.getClass} $e")
  }

  private def allocClosedModuleStruct(module: ClosedModule): (List[IRStmt], IRVarPtr) = {
    val size = I64(fresh("size"))
    val computeSize = IRComputeSize(size, module.struct)
    val structPtr = IRVarPtr(fresh(s"ptr_${module.struct.name}"))
    val malloc = IrCall(structPtr, mallocFun, List(size))

    (List(computeSize, malloc), structPtr)
  }

  private def assignField(path: Path, ptr: IRVarPtr, index: Int, value: IROperand): List[IRStmt] = {
    val fieldPtr = IRVarPtr(fresh(s"ptr_${path}_field_index${index}"))
    val getElement = IRGetElement(fieldPtr, closedModules(path).struct, ptr, index)
    val store = IRStore(value, fieldPtr)
    List(getElement, store)
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