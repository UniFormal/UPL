package info.kwarc.p

// contains all predefined builtins
object Builtins {
  var Applications : Seq[BuiltinApplication] = Seq(
    BuiltinApplication("print", x => {println(x.head match {
      case s: StringValue => s.value
    }); null})
  )
}