// UPL provides a number of operators that are parsed as unresolved and disambiguated during type-checking.

// Possible operators and their concrete syntax are
// - infix o       x o y
// - prefix o      o x
// - postfix o     x o
// - circumfix b   b xs b'
// - applyfix b    x b ys b'
// - bindfix q     q vars. x   
// where o, b, q are symbolic strings with the following properties
// - q (quantifier/binder): contains a unicode symbol described as "N-ary" or "quantifier"
// - b (opening bracket): contains a unicode symbol for starting punctuation; in that case b' is like b but with all those symbols mirrored
// - o: not a binder or bracket


// There are two ways to direct type-checking how to elaborate these operators: magic functions and notations.

module Notations {
  // Magic functions are functions of special names that are declared in a theory.
  // They are used to resolve operators when an instance of the theory is the first argument.
  theory A {
    x: int
    // magic prefix operator: $a becomes a._prefix_$(); here: add 1 to x
    val _prefix_$ = () -> A{x=..x+1}
    // magic infix operator: a ++ n becomes a._infix_++(n); here: add n to x
    val _infix_++ = (y: int) -> A{x=..x+y}
    // magic circumfix operator: 〈a,b,c〉 becomes a._circumfix_〈_〉(list[b,c]); here: sum a.x + b.x + c.x
    val _circumfix_〈_〉 = (as: list[A]) -> {
      var i = x
      for (u in as) i = i+u.x
      A{x=i}
    }
    // magic postfix operator: a⁻ becomes a._prefix_⁻; here: substract 1 from x
    // to distinguish infix from postfix during parsing, postfix operators are restricted to sub/superscripts
    val _postfix_⁻ = () -> A{x=..x-1}
    // magic applyfix operator: a〈b,c〉 becomes a._applyfix_〈_〉(list[b,c]); here: sum a.x + b.x + c.x
    val _applyfix_〈 = (as: list[A]) -> {
      var i = x
      for (u in as) i = i+u.x
      A{x=i}
    }
  }
  a = A{x=1}
  test = (a++2).x == 3 & 〈a,a,a〉.x == 3 & a〈a,a〉.x == 3 & ($a).x == 2 & a⁻.x == 0

  // There are magic functions that are used for converting instances to other types.A
  // - toString: converts to a string, e.g., for printing
  // - elements: converts to a list, for use in a for-loop
  // A special case is "type univ", which is used to convert instances to types (see below).
  // Some of them take additional arguments:
  // - apply: converts to a function, for the notation i(...)
  // - component_n for a number n: converts to a projection function, for the notation i(n)


  // Notations are ascribed to constants using #.
  // They are used when the expected type or the argument types can be used to find a theory T in which a matching notation is found.

  theory Commutative {
    type univ
    // a binary infix operation
    op: (univ,univ) -> univ # infix ∘
    // T is the current theory if an atomic type is encountered that is declared in T.
    comm: |- forall x,y. x∘y == y∘x
  }

  // Notations are also available from the outside if the type i.a is encountered where i:T is an instance of T and a is declared in T.
  testNotation1 = (c: Commutative, x: c.univ) -> x∘x
  testNotation2: (c: Commutative) -> (_,_) -> c.univ = c -> (x,y) -> x∘x
  // Here ".univ" is redundant because it is inserted by the magic conversion of instances to types.  
}
