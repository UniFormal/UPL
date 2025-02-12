package info.kwarc.p

abstract class JS {
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

case class JVarDecl(name: String, init: JS) extends JS {
  override def toString = s"let $name = $init"
}
case class JVarRef(name: String) extends JS {
  override def toString = name
}

case class JBlock(exprs: List[JS]) extends JS {
  override def toString = "{" + exprs.map(_.toString + ";") + "}"
}
case class JWhile(cond: JS, body: JS) extends JS {
  override def toString = s"while ($cond) $body"
}
case class JReturn(exp: JS) extends JS {
  override def toString = s"return $exp"
}
case class JThrow(exp: JS) extends JS {
  override def toString = s"throw $exp"
}

case class JIf(cond: JS, thn: JS, els: Option[JS]) extends JS {
  override def toString = s"if ($cond) $thn" + els.map(" else " + _.toString).getOrElse("")
}
case class JTernary(cond: JS, thn: JS, els: JS) extends JS {
  override def toString = s"($cond) ? $thn : $els"
}

case class JObject(fields: List[(String,JS)]) extends JS {
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
