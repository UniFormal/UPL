package info.kwarc.p

import java.io.{BufferedWriter, OutputStreamWriter}
import scala.collection.mutable.ListBuffer
import scala.io.Source
import scala.util.Using
import java.nio.file.{Files, Paths}

object CompilerLLVM {

  var theories: ListBuffer[llvmTheory] = ListBuffer[llvmTheory]()


  def generateBinary(proj: Project): Unit = {
    var objectFiles: ListBuffer[String] = ListBuffer[String]()
    proj.entries.foreach(entry =>{val llvmIR = generateForEntry(entry)
      val proc = new ProcessBuilder("llc", "-filetype=obj").redirectErrorStream(true).start()
      val writer = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream))
      writer.write(llvmIR)
      writer.write(s"""declare i32 @printf(ptr noundef, ...) #2
                      |
                      |define dso_local noundef i32 @main() {
                      |entry:
                      |   %v = alloca %theory.Theories.Man
                      |   call void @Theories.Man(ptr noundef nonnull align 8 dereferenceable(6) %v)
                      |   call void @Theories.Man.print(ptr noundef nonnull align 8 dereferenceable(6) %v)
                      |  ret i32 0
                      |}""".stripMargin)
      writer.flush()
      writer.close()
      val module = entry.source.container.split('/').last + ".o"
      objectFiles += module
      Using.resource(proc.getInputStream) { in =>
        Files.copy(in, Paths.get(module))
      }
    })

    val sourceFileWithPath = objectFiles.map(x => Paths.get(System.getProperty("user.dir"), x).toString)

    val args: Seq[String] = Seq("clang") ++ sourceFileWithPath ++ Seq("-o", "binary", "-no-pie")
    val process = new ProcessBuilder(args: _*).redirectErrorStream(true).start()
    Source.fromInputStream(process.getInputStream).getLines().foreach(x => println(x))
    objectFiles.foreach(x => Files.deleteIfExists(Paths.get(x)))

  }

  //generate IR for each file
  def generateForEntry(entry: ProjectEntry): String = {
    var contents: String = ""

    entry.parsed.decls.foreach { x =>
      processDeclarations(x, null)
    }
    theories.foreach(x=> {
      contents += x
    })
    theories.foreach(x=> {
      if (x.globalDeclarations.nonEmpty){
        x.globalDeclarations.foreach(y => contents += y + "\n")
      }
    })
    return contents
  }

  //+ expressions
  //+ theory
  private def processDeclarations(decl: Declaration, parent: Module): Unit = {
    decl match {
      case m: Module => {
        // new Theory... internally represented as a closed module... converted to struct
        if (m.closed) {

          val values: ListBuffer[llvmAttribute] = ListBuffer[llvmAttribute]()

          m.childrenInContext.foreach(child => {

            val dataType = processAttribute(child._3, parent)
            if (dataType.isDefined){
              values.addAll(dataType.get)
            }
          })
          theories += llvmTheory(getStructName(m, parent), values.toList)
        } else {
          m.df.decls.foreach(x => processDeclarations(x, m)) //parse all declarations under module
        }
      }
      case exp: ExprDecl => {
        //Top level expression instance = Person{name = "", age = 0}
        //create a new instance of the attribute
        //TODO collect all expressions. evaluated after first pass instantiated all theories

        return None
      }
      case x: TheoryValue => { //new theory
      }
    }
  }

  def getStructName(struct: Module, parent: Module): String = {
    parent.name + "." + struct.name
  }


  private def toLLVMtype(t: Type): llvmType = { //TODO check for other types
    t match {
      case BoolType => llvmTypeBool()
      case NumberType.Int => llvmTypeInt32() //TODO differentiate between numbers
      case NumberType.Float => llvmTypeNone()
      case StringType => llvmTypePtr()
      case funType: FunType => llvmTypeNone()
      case proofType: ProofType => llvmTypeNone()
      case closedRef: ClosedRef => llvmTypeNone()
      case _ => throw IError("invalid type")

    }
  }

  private def processAttribute(attribute: SyntaxFragment, parent: Module): Option[List[llvmAttribute]] = {
    attribute match {
      case inc: Include => {
        //Apply all elements of included theory to the current one
        val includedTheory = parent.name + "." + inc.dom.label
        val ref = theories.find(x => x.name == includedTheory)
        if (ref.nonEmpty){
          return Option(ref.get.values)
        }else{
          //TODO included Theory not yet processed ... operation needs to be delayed
          None
        }
      }
      case exprDecl: ExprDecl => {
        if (exprDecl.dfO == None) {
          val t = toLLVMtype(exprDecl.tp)
          Option(List[llvmValue]{llvmValue(attribute.label, t)})
          //simple attribute
        } else {
          // virtual variable: needs to be converted to a method and the current object passed as parameter
          //child._3.dfO.value == Application
          //value.fun.operator.symbol
          //compiler has AST with n edges
          // needs to call recursively the AST nodes
          exprDecl.dfO.get match {
            case a: Application => None
            case b: BoolValue => Option(List[llvmAttribute]{llvmAssignment(exprDecl.name, if (b.v) "1" else "0")})
            case i: NumberValue => {
              i.tp match {//TODO match other types
                case NumberType.Int => Option(List[llvmAttribute]
                  {llvmAssignment(exprDecl.name, i.value.asInstanceOf[Tuple2[Rat, Rat]]._1.enu.toString())})
              }
            }
            case _ => None
          }
        }
      }
      case typeDecl: TypeDecl => {

        return None
      }

    }
  }

}