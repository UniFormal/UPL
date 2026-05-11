package info.kwarc.p

import scala.collection.mutable.ListBuffer

//type representation in LLVM-IR
sealed trait llvmType {
  //the type in LLVM-IR
  def representation: String
  // the size in bytes
  def size: Int
}
case class llvmTypeBool() extends llvmType {
  override def representation: String = "i8"
  override def size: Int = 1
}
case class llvmTypeInt32() extends llvmType{
  override def representation: String = "i32"
  override def size: Int = 4
}
case class llvmTypePtr() extends llvmType{
  override def representation: String = "ptr"
  override def size: Int = 1
}
case class llvmTypeNone() extends llvmType{
  override def representation: String = ""
  override def size: Int = 0
}
sealed trait globalDeclaration {
  val globalDeclarations: ListBuffer[String]
}

class llvmAttribute()
case class llvmValue(name: String, llvmType: llvmType) extends llvmAttribute
case class llvmAssignment(name: String, initialValue: String) extends llvmAttribute


case class llvmTheory(name: String, values: List[llvmAttribute]) extends globalDeclaration {

  def createConstructor(): String = {
    if (hasConstructor()){//TODO alignment

      var parameterAssignments: String = ""

      getValueAssignments.foreach(x => {
        val index = getValueAttributes.indexWhere(z => z.name == x.name)  //get index of data field inside the structure
        val valueField = getValueAttributes(index)

        parameterAssignments +=
          s"""
              |  %${x.name} = getelementptr %theory.$name, ptr %this, i32 0, i32 $index
              |  store ${valueField.llvmType.representation} ${x.initialValue}, ptr %${x.name}
              |""".stripMargin
      })
      s"""define linkonce_odr dso_local void @$name (ptr noundef nonnull align 8 dereferenceable($size) %this) unnamed_addr {
         |  $parameterAssignments
         |  ret void
         |}""".stripMargin
    }else{
      ""
    }
  }

  def hasConstructor(): Boolean ={
    getValueAssignments.nonEmpty
  }

  private def getValueAttributes: List[llvmValue] = {
    values.collect{case v: llvmValue => v}
  }
  private def getValueAssignments: List[llvmAssignment] = {
    values.collect{case a: llvmAssignment => a}
  }

  private def size(): Int = {
    var dataSize = 0
    getValueAttributes.foreach(v => dataSize += v.llvmType.size)
    dataSize
  }

  private def createPrint(): String = {
    if (values.isEmpty || size() == 0){
      return ""
    }
    var printfParamList, printfInstructions, printfLlvmParamList = ""

    var idx = 0
    getValueAttributes.foreach(x =>{
        x.llvmType match {
          case llvmTypeInt32() => printfParamList += s", ${x.name}: %d"
          case llvmTypeBool() => printfParamList += s", ${x.name}: %d"
          case llvmTypePtr() => printfParamList += s", ${x.name}: %s"
          case _ =>
        }
      printfInstructions += s"""|%${x.name} = getelementptr inbounds nuw %theory.$name, ptr %this, i32 0, i32 $idx
      |   %${x.name}${idx} = load ${x.llvmType.representation}, ptr %${x.name}, align ${x.llvmType.size}
      """.stripMargin
      printfLlvmParamList += s", ${x.llvmType.representation} noundef %${x.name}$idx"
      idx += 1
    })
    printfParamList = s"$name[${printfParamList.substring(2)}]"
    val printString = "theory." + name + ".print.str";
    //+2 for \n; \00
    globalDeclarations += (s"""@$printString = private unnamed_addr constant [${printfParamList.length+2} x i8] c\"${printfParamList}\\0A\\00\", align 1""")
    s"""define linkonce_odr dso_local void @$name.print(ptr noundef nonnull align 8 dereferenceable($size) %this) unnamed_addr {
       |$printfInstructions
       |   %call = call i32 (ptr, ...) @printf(ptr noundef @$printString $printfLlvmParamList)
       |   ret void
       |}""".stripMargin
  }

  //TODO support nested modules in name
  override def toString: String = {
    var paramList = ""
    getValueAttributes.foreach(x => if (paramList.isEmpty) paramList = x.llvmType.representation else
      paramList += ", " + x.llvmType.representation)

    s"""%theory.$name = type { $paramList }
$createConstructor
$createPrint""".stripMargin
  }

  val globalDeclarations: ListBuffer[String] = ListBuffer[String]()
}