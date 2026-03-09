module Division {

  // UPL: division operator '/' with subtyping, e.g. int->int->rat
  // Isabelle: 'div' operator int->int->int, '/' operator a'::field->a'::field->a'::field (e.g. rat, real, comp), 'Fract' function int->int->rat

  // produces error #49:204: while checking (x / y): ill-typed operator
  int_div1(x,y:: int): int = x / y

  // works in UPL, but doesn't type-check in Isabelle with either div,/; type-checks with Fract
  int_div2(x,y:: int) = x/y // (int,int) -> rat

  // works in UPL and correct, type-checking translation with /
  rat_div(x,y:: rat) = x/y
  comp_div(x,y:: comp) = x/y
  real_div(x,y:: float) = x/y




}