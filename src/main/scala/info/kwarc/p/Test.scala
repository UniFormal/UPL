package info.kwarc.p

object Test {
  def mustFail[A, E <: PError](cls: Class[E])(code: => A): Any = {
    try {
      code
    }
    catch {
      case e: PError if e.getClass == cls =>
      case e => println("test failed: " + e)
    }
  }

  def parse(s: String):Vocabulary = Parser.text(SourceOrigin("test"), s, ErrorThrower)

  def check(s: String): Vocabulary = {
    val v = parse(s)
    new Checker(ErrorThrower).checkVocabulary(GlobalContext("test"), v, keepFull = true)(v)
  }

}

object Tests {
  import Test._

  def main(args: Array[String]):Unit = {
    mustFail(classOf[Parser#Error])(parse("1==1"))
    mustFail(classOf[Checker#Error])(check("1:int"))
    mustFail(classOf[Checker#Error])(check("i:[int]=[1,2,3,4]"))
    mustFail(classOf[Checker#Error])(check("append : [int] -> [int] -> [int] = l -> m  = l + m"))
    mustFail(classOf[Checker#Error])(check("1+\"a\""))
    mustFail(classOf[Parser#Error])(parse("2==2"))
  }
}
