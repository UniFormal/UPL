// UPL provides a number of operators that are parsed as unresolved and disambiguated during type-checking.

// Possible operators and their concrete syntax are
// - infix o       t o y
// - prefix o      o t
// - postfix o     t o
// - circumfix b   b ts b'
// - applyfix b    t b ys b'
// - bindfix q     q vars . y 
// where 
// - t:T, or ts: list[T] allow for resoving the operator
// - y, ys match the expected type(s),
// o, b and q are symbolic strings with the following properties
// - q (quantifier/binder): contains a unicode symbol described as "N-ary" or "quantifier"
// - b (opening bracket): contains a unicode symbol for starting punctuation; in that case b' is like b but with all those symbols mirrored
// - o: not a binder or bracket
// and vars is a comma separated list of variable declarations (like in a function signature)

// There are two ways to direct type-checking how to elaborate these operators: magic functions and notations. 

module Operators {
  // Magic functions are functions of special names that are declared in a theory.
  // They are used to resolve operators when an instance of the theory is the first argument.
  theory Magic {
    x: int
    // magic prefix operator: $a becomes a._prefix_$(); here: add 1 to x
    val _prefix_$ = () -> Magic{x=..x+1}
    // magic infix operator: a ++ n becomes a._infix_++(n); here: add n to x
    val _infix_++ = (y: int) -> Magic{x=..x+y}
    // magic circumfix operator: 〈a,b,c〉 becomes a._circumfix_〈(list[b,c]); here: sum a.x + b.x + c.x
    // the respective closing operator is determined automatically from the unicode specification
    val _circumfix_〈 = (as: list[Magic]) -> {
      var i = x
      for (u in as) i = i+u.x
      Magic{x=i}
    }
    // magic postfix operator: a⁻ becomes a._postfix_⁻; here: substract 1 from x
    // to distinguish infix from postfix during parsing, postfix operators are restricted to sub/superscripts
    val _postfix_⁻ = () -> Magic{x=..x-1}
    // magic applyfix operator: a〈b,c〉 becomes a._applyfix_〈(list[b,c]); here: sum a.x + b.x + c.x
    // the respective closing operator is determined automatically from the unicode specification
    val _applyfix_〈 = (as: list[Magic]) -> {
      var i = x
      for (u in as) i = i+u.x
      Magic{x=i}
    }
  }
  a = Magic{x=1}
  test = {ASSERT((a++2).x,3); ASSERT(〈a,a,a〉.x,3); ASSERT(a〈a,a〉.x,3); ASSERT(($a).x, 2);  ASSERT(a⁻.x, 0)}

  // There are magic functions that are used for converting instances to other types.
  // - toString: converts to a string, e.g., for printing
  // - elements: converts to a list, for use in a for-loop
  // A special case is "type univ", which is used to convert instances to types (see below).
  // Some of them take additional arguments:
  // - apply: converts to a function, for the notation i(...)
  // - component_n for a number n: converts to a projection function, for the notation i(n)


  // Notations are ascribed to constants using #.
  // They are used when the expected type or the argument types can be used to find a theory T in which a matching notation is found.

  theory Notation {
    type univ
    // a binary infix operation
    op: (univ,univ) -> univ # infix ∘
    // T is the current theory if an atomic type is encountered that is declared in T.
    comm: |- forall x,y. x∘y == y∘x
  }

  // Notations are also available from the outside if the type i.a is encountered where i:T is an instance of T and a is declared in T.
  testNotation1 = (c: Notation, x: c.univ) -> x∘x
  testNotation2: (c: Notation) -> (_,_) -> c.univ = c -> (x,y) -> x∘x
  // Here ".univ" is redundant because it is inserted by the magic conversion of instances to types.  
}
