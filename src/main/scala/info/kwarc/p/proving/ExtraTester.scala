package info.kwarc.p.proving

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import info.kwarc.p._

object TPTPTranslatorSummary {
  private case class SummaryCase(
    label: String,
    input: String,
    actual: () => String,
    expected: String,
    mustContain: List[String] = Nil,
    mustNotContain: List[String] = Nil
  )

  private def normalize(output: String): String =
    output.linesIterator
      .map(_.trim)
      .filter(_.nonEmpty)
      .mkString("\n")
      .replaceAll("\\s+", "")

  private def report(testCase: SummaryCase): Boolean = {
    println(s"\n--- ${testCase.label} ---")
    println("input:")
    println(testCase.input)
    try {
      val actual = normalize(testCase.actual())
      val expected = normalize(testCase.expected)
      println("output:")
      println(actual)

      if (testCase.expected.nonEmpty) {
        println("expected:")
        println(expected)
      } else {
        println("expected fragments:")
        testCase.mustContain.foreach(fragment => println(normalize(fragment)))
      }

      val exactMatch = testCase.expected.isEmpty || actual == expected
      val containsMatch = testCase.mustContain.forall(fragment => actual.contains(normalize(fragment)))
      val excludesMatch = testCase.mustNotContain.forall(fragment => !actual.contains(normalize(fragment)))

      if (exactMatch && containsMatch && excludesMatch) {
        println(s"[OK]   ${testCase.label}")
        true
      } else {
        if (!exactMatch) println(s"Expected output differs for ${testCase.label}")
        testCase.mustContain.filterNot(fragment => actual.contains(normalize(fragment))).foreach { fragment =>
          println(s"[MISSING] ${normalize(fragment)}")
        }
        testCase.mustNotContain.filter(fragment => actual.contains(normalize(fragment))).foreach { fragment =>
          println(s"[UNEXPECTED] ${normalize(fragment)}")
        }
        println(s"[FAIL] ${testCase.label}")
        false
      }
    } catch {
      case error: Throwable =>
        println("output:")
        println(s"<error: ${error.getMessage}>")
        if (testCase.expected.nonEmpty) {
          println("expected:")
          println(normalize(testCase.expected))
        } else {
          println("expected fragments:")
          testCase.mustContain.foreach(fragment => println(normalize(fragment)))
        }
        println(s"[ERROR] ${testCase.label}: ${error.getMessage}")
        false
    }
  }

  def main(args: Array[String]): Unit = {
    val basicsInput =
      """
        |
        |   type a = int
        |   val c1: a = 0
        |   c2 = 0
        |
      """.stripMargin

    val basicsExpected =
      """
        thf(c1_type, type, c1 : $int).
        thf(c1_def,  axiom, (c1 = 0)).

        
        thf(c2_type, type, c2 : $int).
        thf(c2_def,  axiom, (c2 = 0)).

        thf(goal,conjecture,$true).
      """.stripMargin

    val unitInput =
      """
        |
        |   type a = int
        |   val u: unit = ()
        |   val c1: a = 0
        | 
      """.stripMargin

    val unitExpected =
      """
        thf(unit_type,type,unit:$tType).
        thf(unit_value_type,type,unit_value:unit).
        thf(unit_unique,axiom,(![X:unit]:(X=unit_value))).
        thf(u_type,type,u:unit).thf(u_def,axiom,(u=unit_value)).
        thf(c1_type,type,c1:$int).
        thf(c1_def,axiom,(c1=0)).
        thf(goal,conjecture,$true).""".stripMargin

    val newestTest =
      """ |t: (x:int,s:string) = (1,"foo")
          |t_1: int = t(1)""".stripMargin

    val functions =
      """
        |f1 : int -> int = (X:int) -> X+1
        |f2 = (X:int) -> X+1
        |f3 : int -> int = X -> X+1
        |f4 : int -> _ = X -> X+1
        |f5_multiarg: (int,int) -> int = (X,Y) -> X+Y
        |f5_multiarg_applied = f5_multiarg(0,1)
        |f5_curried:   int -> int -> int = X -> Y -> X+Y
        |f5_curried_applied = f5_curried(0)(1)
        |f5_multiarg_variant(X: int,Y:int): int = X+Y
      """.stripMargin

    val bigtest =
      """
        theory Carrier {
    type univ
  }
  theory Relation {
    include Carrier
    rel: (univ,univ) -> bool # infix %  // # declares notation
  }
  theory Reflexive {
    include Relation
    refl:--- x % x  // :--- abbreviates axiom for universal closure
  }
  theory Transitive {
    include Relation
    trans:--- x%y & y%z => x%z
  }
  theory Symmetric {
    include Relation
    sym:--- x%y => y%x
  }
  theory Preorder {
    include Reflexive
    include Transitive
  }
  theory PER {
    include Symmetric
    include Transitive
  }
  theory Equivalence {
    include PER
    include Preorder
  }
  theory SubCarrier {
    include Carrier
    per: PER {type univ = ..univ}  // .. accesses surrounding theory
    perapply # infix % = per.rel
  }
  theory Magma {
    include Carrier
    op: (univ,univ) -> univ # infix ∘
  }
  theory SubMagma {
    include SubCarrier
    include Magma
    op_per:--- x1 % y1 & x2 % y2 => (x1∘y1) % (x2∘y2)
  }
  theory Semigroup {
    include Magma
    assoc:--- x∘(y∘z) == (x∘y)∘z
  }
  theory Abelian {
    include Magma
    comm:--- x∘y == y∘x
  }
  theory Pointed {
    include Magma
    e: univ
  }
  theory Monoid {
    include Pointed
    neutL:--- e∘x==x
    neutR:--- x∘e==x
  }
  theory SubMonoid {
    include SubMagma
    include Monoid
    e_per:--- e % e
  }
  theory Idempotent {
    include Magma
    idem:--- x∘x==x
  }
  theory Semilattice {
    include Abelian
    include Idempotent
  }
  theory BoundedSemilattice {
    include Semilattice
    include Monoid
  }
  theory Group {
    include Monoid
    inv: univ -> univ # postfix ⁻
    invL:--- x∘x⁻ == e
    invR:--- x⁻ ∘ x == e
  }
  theory SubGroup {
    include SubMonoid
    include Group
    inv_per:--- x % y => x⁻ % y⁻
  }
  theory AbelianGroup {
    include Group
    include Abelian
  }

  // for theory H:
  // H {d1, ...} abbreviates {include H, d1, ...}
  theory BiMagma {
    include Carrier
    // add must be a model of {type univ == ..univ, op: (univ,univ) -> univ}
    add  : Magma {type univ = ..univ} // .. accesses surrounding theory
    mult : Magma {type univ = ..univ}
  }
  // intAdd is a model of Magma, by extending it with definitions for all abstract fields
  intAdd  = Magma {type univ = int, op = (x,y) -> x+y}
  intMult = Magma {type univ = int, op = (x,y) -> x*y}
  intAddMult = BiMagma {type univ = int, add = intAdd, mult = intMult}

  theory Rng {
    include BiMagma
    add:  AbelianGroup
    mult: Semigroup
  }
  theory Ring {
    include Rng
    mult: Monoid
  }
  theory AbelianRing {
    include Ring
    mult: Abelian
  }
  theory SemiField {
    include AbelianRing
    mult: SubGroup {
      per = PER {
        rel = (x,y) -> x == y & x != e
        sym = ???
        trans = ???
      }
    }
    inv_zero:--- mult.inv(add.e) == add.e
  }
  theory Field {
    include SemiField
    mult: Abelian

    goal:--- mult.inv(add.e) == add.e
  }
      """.stripMargin
    val parseExpr = (src: String) => Parser.expression(SourceOrigin("ExtraTester"), src, ErrorThrower)
    val parseTheory = (src: String) => Parser.text(SourceOrigin("ExtraTester"), src, ErrorThrower)
    val translateInput = (input: String) => TPTPTranslator(parseTheory(input), BoolValue(true)).toString

    val basicsWithGoal =
      """
        |type a = int
        |val c1: a = 0
        |c2 = 0
        |goal:--- c1 == 0
      """.stripMargin

    val unitWithGoal =
      """
        |val u: unit = ()
        |goal:--- u == ()
      """.stripMargin

    val natWithGoal =
      """
        |val n: nat = 1
        |goal:--- n >= 0
      """.stripMargin

    val algebraOutsideGoal =
      bigtest.replace("    goal:--- mult.inv(add.e) == add.e", "") +
        "\n\ngoal:--- x % x\n"

    val testCases = List(
      SummaryCase(
        "Basics001 module",
        basicsInput,
        () => TPTPTranslator(Parser.text(SourceOrigin("ExtraTester"), basicsInput, ErrorThrower), BoolValue(true)).toString,
        basicsExpected
      ),
      SummaryCase(
        "basics001 with unit in parsed module",
        unitInput,
        () => TPTPTranslator(Parser.text(SourceOrigin("ExtraTester"), unitInput, ErrorThrower), BoolValue(true)).toString,
        unitExpected
      ),
      SummaryCase(
        "Basics001 with a top-level input goal",
        basicsWithGoal,
        () => TPTPTranslator(parseTheory(basicsWithGoal), BoolValue(false)).toString,
        """thf(c1_type,type,c1:$int).
          |thf(c1_def,axiom,(c1=0)).
          |thf(c2_type,type,c2:$int).
          |thf(c2_def,axiom,(c2=0)).
          |thf(goal,conjecture,(c1=0)).""".stripMargin,
        mustNotContain = List("thf(goal,conjecture,$false)", "thf(goal,conjecture,$true)")
      ),
      SummaryCase(
        "Direct goal passed as an Expression (no input goal scan)",
        "val c1: int = 0; goal is passed directly as an Expression",
        () => TPTPTranslator.applyDirect(parseTheory("val c1: int = 0"), parseExpr("c1 == 0")).toString,
        """thf(c1_type,type,c1:$int).
          |thf(c1_def,axiom,(c1=0)).
          |thf(goal,conjecture,(c1=0)).""".stripMargin
      ),
      SummaryCase(
        "Unit declaration with an equality goal",
        unitWithGoal,
        () => translateInput(unitWithGoal),
        "",
        mustContain = List(
          "thf(unit_type,type,unit:$tType).",
          "thf(unit_value_type,type,unit_value:unit).",
          "thf(unit_unique,axiom,(![X:unit]:(X=unit_value))).",
          "thf(u_type,type,u:unit).",
          "thf(u_def,axiom,(u=unit_value)).",
          "thf(goal,conjecture,(u=unit_value))."
        ),
        mustNotContain = List("thf(goal,conjecture,$true)")
      ),
      SummaryCase(
        "Nat declaration with a non-negativity goal",
        natWithGoal,
        () => translateInput(natWithGoal),
        "",
        mustContain = List(
          "thf(nat_type,type,nat:$tType).",
          "thf(nat_def,definition,(nat=$int)).",
          "thf(nat_nonnegative,axiom,(![N:nat]:(($greatereq@N)@0))).",
          "thf(n_type,type,n:nat).",
          "thf(n_def,axiom,(n=1)).",
          "thf(goal,conjecture,($greatereq@n@0))."
        ),
        mustNotContain = List("thf(goal,conjecture,$true)")
      ),
      SummaryCase(
        "false conjecture",
        "false",
        () => TPTPTranslator(Theory(Nil), parseExpr("false")).toString,
        "thf(goal,conjecture,$false)."
      ),
      SummaryCase(
        "AppliedRef instantiation",
        "id@(A,B)",
        () => TPTPTranslator(Theory(Nil), parseExpr("id@(A,B)")).toString,
        "thf(goal,conjecture,((id @ A) @ B))."
      ),
      SummaryCase(
        "non-unit formula stays clean",
        "true",
        () => TPTPTranslator(Theory(Nil), parseExpr("true")).toString,
        "thf(goal,conjecture,$true)."
      ),
      SummaryCase(
        "unit literal not usable case",
        "()",
        () => TPTPTranslator(Theory(Nil), parseExpr("()")).toString,
        """thf(unit_type,type,unit : $tType).
          |thf(unit_value_type,type,unit_value : unit).
          |thf(unit_unique,axiom,(! [X : unit] : (X = unit_value))).
          |thf(goal,conjecture,(unit_value = unit_value)).""".stripMargin
      ),
      
      SummaryCase(
        "Tuple, Projection Test (currently wrong due to tuples not working in LEO-III and needing something simillar to tables if it goes past a pair)",
        newestTest,
        () => TPTPTranslator(Parser.text(SourceOrigin("ExtraTester"), newestTest, ErrorThrower), BoolValue(true)).toString,
        "expected"
      )
      
      ,SummaryCase(
        "functions, with some errors due to things like f2 = x and such making translation harder",
        functions,
        () => TPTPTranslator(Parser.text(SourceOrigin("ExtraTester"), functions, ErrorThrower), BoolValue(true)).toString,
        "expected"
      )
      ,SummaryCase(
        "Algebra.p: goal inside the named Field theory",
        bigtest,
        () => translateInput(bigtest),
        "",
        mustContain = List(
          "thf(owned_semiField_refinement_inv_zero,axiom,((owned_semiField_mult_inv@owned_add_e)=owned_add_e)).",
          "thf(goal,conjecture,((owned_field_mult_inv@owned_add_e)=owned_add_e))."
        ),
        mustNotContain = List("thf(goal,conjecture,$true)")
      ),
      SummaryCase(
        "Algebra.p: goal outside all theories",
        algebraOutsideGoal,
        () => translateInput(algebraOutsideGoal),
        "",
        mustContain = List("thf(goal,conjecture,(![X:univ]:((perapply@X)@X)))."),
        mustNotContain = List("thf(goal,conjecture,$true)")
      )
    )

    println("TPTP translator detailed report")
    val results = testCases.map(report)
    println("\nTPTP translator test summary")
    val passed = results.count(identity)
    val failed = testCases.size - passed
    println(s"Result: $passed passed, $failed failed, ${testCases.size} total")
  }
}
