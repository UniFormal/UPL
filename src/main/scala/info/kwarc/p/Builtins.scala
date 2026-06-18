package info.kwarc.p

// contains all predefined builtins
object Builtins {
  case class BuiltinDefinition(name: String, parameters: List[Type], returnType: Type){
  }

  var Builtins: Seq[BuiltinDefinition] = Seq(
    BuiltinDefinition("print", List[Type] {
      StringType
    }, EmptyType),
    BuiltinDefinition("read", List.empty[Type], StringType)
  )
}