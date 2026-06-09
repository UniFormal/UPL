//> using dep org.scala-lang.modules::scala-parser-combinators:2.4.0

package info.kwarc.p.proving

import scala.util.parsing.combinator._

abstract class TPTP {

}

case class TPTPFile(decls: List[TPTPDecl]) extends TPTP {
  override def toString: String = decls.mkString("\n")
}

case class TPTPDecl(id: String, role: String, formula: TPTPFormula) extends TPTP {
  override def toString = s"thf($id,$role,$formula)."
}

case class TPTPContext(decls: List[(String,TPTPFormula)]) extends TPTP
    {
        override def toString = {
            decls.map { case (v,t) => s"$v : $t"}.mkString(", ")
        }
    }


abstract class TPTPFormula extends TPTP

case class FunType(domain: TPTPFormula, range: TPTPFormula) extends TPTPFormula {
    override def toString = s"($domain > $range)"
}

case class TypeAssignment(ident: TPTPFormula, tpe: TPTPFormula) extends TPTPFormula {
    override def toString = s"$ident : $tpe"
}

case class Constant(name : String) extends TPTPFormula {
    override def toString = name
  }

case class Variable(name : String) extends TPTPFormula {
    override def toString = name.capitalize
  }

case class Apply(fun: TPTPFormula, arg: TPTPFormula) extends TPTPFormula {
    override def toString = s"($fun @ $arg)"
  }

case class Quantifier(univ: Boolean, vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
  override def toString = {
    val q = if (univ) "!" else "?"
    s"($q[$vars]:$body)"
  }
}

case class Lambda(vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(^ [$vars] : $body)"
}

case class Conjunction(left: TPTPFormula, right: TPTPFormula) extends TPTPFormula
    {
        override def toString = s"($left & $right)"
    }

case class Implication( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString = s"($left => $right)"
}

case class Equivilant( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString = s"($left <=> $right)"
}

case class Disjunction( left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
  override def toString = s"($left | $right)"
}

case class Equality(isEqual: Boolean, L: TPTPFormula, R: TPTPFormula) extends TPTPFormula {
    override def toString = {
        val e = if (isEqual) "=" else "!="
        s"($L $e $R)"
  }
}

case class Negation(body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(~ $body)"
}

case class InterpretedConstant(name: String) extends TPTPFormula {
    override def toString = if (name.startsWith("$")) name else s"$$$name"
}

case class Choice(isDefinite: Boolean, vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = {
      val cb = if (isDefinite) "@-" else "@+"
      s"($cb[$vars]:$body)"
  }
}

case class Xor(left: TPTPFormula, right: TPTPFormula) extends TPTPFormula {
    override def toString: String = s"($left <~> $right)"
}

case class IfThenElse(cond: TPTPFormula, thn: TPTPFormula, els: TPTPFormula) extends TPTPFormula {
    override def toString: String = s"$$ite($cond, $thn, $els)"
}

case class TypeQuantifier(vars: TPTPContext, body: TPTPFormula) extends TPTPFormula {
    override def toString = s"(!> [$vars] : $body)"
}

//Missing UPL Syntax Knowledge for more precise Translation and search
//Placeholder/Logical search 

class UPLParser extends RegexParsers {

    def formula: Parser[TPTPFormula] = 
        implication | conjunction | equivilant | disjunction | simpleFormula | choice | xor | ifthenelse | typequantifier

    def simpleFormula: Parser[TPTPFormula] = (
        quantifier
        | negation 
        | lambda 
        | applyExpr 
        | variable 
        | constant 
        | "(" ~> formula <~ ")" 
    )
  
    def module: Parser[TPTPFile] = 
        "module" ~> """[a-zA-Z0-9_]+""".r ~ ("{" ~> rep(declaration) <~ "}") ^^ {
            case name ~ declsList => TPTPFile(declsList.flatten)
        }
    
    def declaration: Parser[List[TPTPDecl]] = typeDecl | valDecl

    def typeDecl: Parser[List[TPTPDecl]] = 
    "type" ~> """[a-z][a-zA-Z0-9_]*""".r ~ ("=" ~> """[a-z][a-zA-Z0-9_]*""".r) ^^ {
    case typeName ~ baseType => 
      List(TPTPDecl(
        id = s"${typeName}_type",
        role = "type", 
        formula = TypeAssignment(Constant(typeName), Constant("$tType")) 
      ))
    }

    def valDecl: Parser[List[TPTPDecl]] = 
    opt("val") ~> """[a-z][a-zA-Z0-9_]*""".r ~ opt(":" ~> """[a-z][a-zA-Z0-9_]*""".r) ~ ("=" ~> """[0-9]+""".r) ^^ {
    case varName ~ maybeType ~ value =>
      
      val typeName = maybeType.getOrElse("$i")
      
      val typeDecl = TPTPDecl(
        id = s"${varName}_type", 
        role = "type", 
        formula = TypeAssignment(Constant(varName), Constant(typeName)) 
      )
      
      val axiomDecl = TPTPDecl(
        id = s"${varName}_def", 
        role = "axiom", 
        formula = Equality(isEqual = true, Constant(varName), Constant(value)) 
      )
      
      List(typeDecl, axiomDecl)
    }

    def constant: Parser[Constant] = """[a-z][a-zA-Z0-9_]*""".r ^^ { name => Constant(name) }
  
    def variable: Parser[Variable] = """[A-Z][a-zA-Z0-9_]*""".r ^^ { name => Variable(name) }



    def quantifier: Parser[Quantifier] = ???
    def lambda: Parser[Lambda] = ???
    def applyExpr: Parser[Apply] = ???
    def negation: Parser[Negation] = ???

    def conjunction: Parser[Conjunction] = formula ~ ("&" ~> formula) ^^ {
        case links ~ rechts => Conjunction(links, rechts)
    }

    def disjunction: Parser[Disjunction] = formula ~ ("|"~> formula) ^^{
        case links ~ rechts => Disjunction(links, rechts)
    }

    def implication: Parser[Implication] = formula ~ ("=>"~> formula) ^^{
        case links ~ rechts => Implication(links, rechts)
    }

    def equivilant: Parser[Equivilant] = formula ~ ("<=>"~> formula) ^^{
        case links ~ rechts => Equivilant(links, rechts)
    }

    def equality: Parser[Equality] = formula ~ ("=" | "!=") ~ formula ^^ {
        case links ~ op ~ rechts => Equality(op == "=", links, rechts)
    }
    
    def choice: Parser[Choice] = ???
    def xor: Parser[Xor] = ???
    def ifthenelse: Parser[IfThenElse] = ???
    def typequantifier: Parser[TypeQuantifier] = ???
    def funtype: Parser[FunType] = ???
}


//Quick Tests

object Main extends App {
  val parser = new UPLParser

  val uplInput = """
    module Basics001 {
      type a = int
      val c1: a = 0
      c2 = 0
    }
  """

 
  parser.parseAll(parser.module, uplInput) match {
    case parser.Success(tptpAst, _) =>
      println(tptpAst.toString)
     
      
    case parser.NoSuccess(error, next) =>
      println(s"Parsing Fehler bei Zeile ${next.pos.line}, Spalte ${next.pos.column}:")
      println(error)
  }

  /*Ausgabe
    thf(a_type,type,a : $tType).
    thf(c1_type,type,c1 : a).
    thf(c1_def,axiom,(c1 = 0)).
    thf(c2_type,type,c2 : $i).
    thf(c2_def,axiom,(c2 = 0)).
  */
}
