package info.kwarc.p

abstract class JS {
  def apply(s: String) = JObjectElem(this, s)
  def apply(args: JS*) = JApply(this, args.toList)
  def equal(that: JS) = JBinOp("===", this, that)
}

case class JInt(value: Int) extends JS {
  override def toString = value.toString
}
case class JBool(value: Boolean) extends JS {
  override def toString = value.toString
}
case class JString(value: String) extends JS {
  override def toString = value.toString
}
case class JUnOp(symbol: String, arg: JS) extends JS {
  override def toString = symbol + arg
}
case class JBinOp(symbol: String, left: JS, right: JS) extends JS {
  override def toString = s"($left $symbol $right)"
}

case class JVarDecl(name: String, init: JS, global: Boolean) extends JS {
  def keyword = if (global) "var" else "let"
  override def toString = s"$keyword $name = $init"
}
case class JVarRef(name: String) extends JS {
  override def toString = name
}
case class JVarDef(name: String, df: JS) extends JS {
  override def toString = name + " = " + df + ";"
}

case class JBlock(exprs: List[JS]) extends JS {
  override def toString = "{" + exprs.map(_.toString + ";") + "}"
  def asExpression() = {
    val esE = exprs match {
      case Nil => Nil
      case es => es.init ::: List(JReturn.prefix(es.last))
    }
    JApply(JFunction(Nil, JBlock(esE)), Nil)
  }
}
case class JWhile(cond: JS, body: JS) extends JS {
  override def toString = s"while ($cond) $body"
}
case class JReturn(exp: JS) extends JS {
  override def toString = s"return $exp"
}
object JReturn {
  def prefix(j: JS): JS = j match {
    case JIf(cond, thn, elsO) => JIf(cond, prefix(thn), elsO map prefix)
    case JTry(t,n,c) => JTry(prefix(t), n, prefix(c))
    case _:JReturn | _:JThrow => j
    case _:JVarDecl | _:JVarDef | _:JWhile => j
    case b: JBlock => prefix(b.asExpression())
    case _ => JReturn(j)
  }
}
case class JThrow(exp: JS) extends JS {
  override def toString = s"throw $exp"
}
case class JTry(tr: JS, exnName: String, ctch: JS) extends JS {
  override def toString = s"try {$tr} catch ($exnName) {$ctch}"
}

case class JIf(cond: JS, thn: JS, els: Option[JS]) extends JS {
  override def toString = s"if ($cond) $thn" + els.map(" else " + _.toString).getOrElse("")
}
case class JTernary(cond: JS, thn: JS, els: JS) extends JS {
  override def toString = s"($cond) ? $thn : $els"
}

case class JObject(fields: (String,JS)*) extends JS {
  override def toString = fields.map(f => f._1 + ":" + f._2).mkString("{", ",", "}")
}
case class JObjectElem(obj: JS, field: String) extends JS {
  override def toString = s"$obj.$field"
}

case class JArray(elems: List[JS]) extends JS {
  override def toString = elems.map(_.toString).mkString("[", ",", "]")
}
case class JArrayElem(arr: JS, index: JS) extends JS {
  override def toString = s"$arr[$index]"
}

case class JFunction(ins: List[String], body: JS) extends JS {
  override def toString = s"function(${ins.mkString(",")}) {$body}"
}
case class JApply(fun: JS, args: List[JS]) extends JS {
  override def toString = s"$fun(${args.mkString(",")})"
}
