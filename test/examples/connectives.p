// Interpretation of the boolean connectives, with the emphasis on =>.
//
// Syntax.scala documents => as "the same as comparison a <= b; but we need a separate
// operator to get the right notation", so the first group below pins the two together.
// Implies is n-ary: the parser collapses a chain into a single Implies node (visible in
// the checker's output), and Operator.simplify folds it right-associatively, so the last
// element is the conclusion and the earlier ones are hypotheses (cf. Checker.applyIntros).
// interpretDynamicBoolean used to treat every false element as a hypothesis, so a false
// conclusion was discharged rather than refuting, and => could never evaluate to false.
module Connectives {
  // => must agree with <= on bool, per the note at Syntax.scala's Implies declaration.
  impl(x,y:: bool): bool = x => y
  le(x,y:: bool): bool   = x <= y
  agreeTT = () -> ASSERT(impl(true,true)  == le(true,true),  true)
  agreeTF = () -> ASSERT(impl(true,false) == le(true,false), true)
  agreeFT = () -> ASSERT(impl(false,true) == le(false,true), true)
  agreeFF = () -> ASSERT(impl(false,false)== le(false,false),true)

  // and the values themselves, so this file does not depend on <= being right either
  t2_TT = () -> ASSERT(true => true,  true)
  t2_TF = () -> ASSERT(true => false, false)
  t2_FT = () -> ASSERT(false => true, true)
  t2_FF = () -> ASSERT(false => false,true)

  // chains: false exactly when every hypothesis holds and the conclusion does not
  t3_TTF = () -> ASSERT(true => true => false, false)
  t3_TTT = () -> ASSERT(true => true => true,  true)
  t3_FTF = () -> ASSERT(false => true => false,true)

  // Precedence comes from the printed width of the operator, so with one space on each
  // side & binds tighter than => and this is (true & true) => false.
  mixed = () -> ASSERT(true & true => false, false)

  // Short-circuiting: the conclusion must not be evaluated when a hypothesis fails.
  // Same property as dynamicImply in basics.p; kept here so this file stands alone.
  guard = () -> ASSERT(false => (1/0 == 1), true)

  // Dynamic binding: names introduced on the left stay visible on the right.
  dynImplies = () -> ASSERT((val x = 1) => x==1, true)
  dynAnd     = () -> ASSERT((val y = 2) & y==2, true)

  // The shape dynamicNames uses in basics.p, exercised both ways round. Before the fix
  // this came out true whether or not z==k held, so that assertion could not fail.
  dynShape      = (l: list[int], k: int) -> (([val u, val v] = l) & (val z = u+v) => z==k)
  dynShapeTrue  = () -> ASSERT(dynShape([1,2], 3),  true)
  dynShapeFalse = () -> ASSERT(dynShape([1,2], 99), false)

  // A declaration as the conclusion evaluates to true; a pattern match as the conclusion
  // evaluates to whether it matched, so a failing match now refutes rather than passing.
  declConclusion  = () -> ASSERT((true => (val w = 1)), true)
  matchConclusion = (l: list[int]) -> (true => ([val u, val v] = l))
  matchHolds      = () -> ASSERT(matchConclusion([1,2]), true)
  matchFails      = () -> ASSERT(matchConclusion([1]),   false)

  test = {
    agreeTT(); agreeTF(); agreeFT(); agreeFF()
    t2_TT(); t2_TF(); t2_FT(); t2_FF()
    t3_TTF(); t3_TTT(); t3_FTF()
    mixed(); guard()
    dynImplies(); dynAnd(); dynShapeTrue(); dynShapeFalse()
    declConclusion(); matchHolds(); matchFails()
    true
  }
}
