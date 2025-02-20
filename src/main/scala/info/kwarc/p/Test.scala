package info.kwarc.p

object Test {
  def mustFail[A, E <: PError](cls: Class[E])(code: => A) = {
    try {code}
    catch {
      case e: PError if e.getClass == cls =>
      case e => println("test failed: " + e)
    }
  }

  def parse(s: String) = Parser.text(SourceOrigin("test"), s, ErrorThrower)

  def check(s: String) = {
    val v = parse(s)
    new Checker(ErrorThrower).checkVocabulary(GlobalContext("test"), v, true)(v)
  }

}

object Tests {
  import Test._

  def main(args: Array[String]) = {
    mustFail(classOf[Parser#Error])(parse("1+"))

    mustFail(classOf[Checker#Error])(check("1+\"a\""))
  }
}
