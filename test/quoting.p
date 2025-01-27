// test file for quotation
module Q {

  // a theory to quote; think of this a context-free grammar or as a set of inductive data types
  // Here we use the natural numbers.
  theory N {
    type n
    z: n
    s: n -> n
  }

  // introduction rule: Q |- N{t}: N{A}: type   if   N |- t:A:type
  // we call N{t} the quotation of t, and N{A} the type of quotations
  
  // elimination rule: within a quotation, `e` can be used to evaluate an expression from Q
  // i.e., N |- `e`: A  if  Q |- e: N{A}
  // representation rule (analogue of eta): Q |- e == N{`e`}
  // computation rule (analogue of beta):   N |- `N{t}` == t 

  zero = N{z}
  one = N{s(z)}
  two = N{s(`one`)}
  succ = (x:N{n}) -> N{s(`x`)}
  pred = x -> x match {
    N.z -> []
    N{s(`p`)} -> [p]
  }

  test1 = (succ(zero) == one) & (pred(two) == [one])

  // For the most important case, where the quoted term/type is just a name, .id can be used instead of {id}:
  alsoZero: N.n = N.z

  // Quoted functions f:N{A->B} induce functions f*:N{A}->N{B} on quotations by putting f* = x -> N{`f`(`x`)}
  // This operation is so important that f is automatically coerced to f* if it is applied to arguments.
  // With this coercion in place, quoted constants can be used like constructors of inductive types:
  alsoSucc: N.n -> N.n = x -> N.s(x)

  // The converse is not true: There are functions N{A}->N{B} that are not induced by a quotation, e.g., pred: N.n -> N.n above.
  // This is the difference between functions N{A}->N{B} that are
  // - derivable by the syntax (by an expression f:A->B) or
  // - only admissible by a definition about the syntax.

  // Note that the definition of pred cannot be moved into N: Within N, the type n is still open and induction on it is not allowed.
  // Indeed, we can add more terms to N to obtain the language of the integers:

  theory Z {
    include N
    p: n -> n
  }

  // Inclusion between theories yields subtyping of quotation types:
  oneInZ : Z.n = one

  normalize: Z.n -> Z.n
  normalize = x -> x match {
    Z.z -> Z.z
    Z.s(y) -> normalize(y) match {
      Z.p(u) -> u
      u -> Z.s(u)
    }
    Z.p(y) -> normalize(y) match {
      Z.s(u) -> u
      u -> Z.p(u)
    }
  }

  test2 = normalize(Z{s(p(p(s(z))))}) == Z.z

  // This also works for languages with higher-order functions:

  theory FOL {
    type term
    type prop
    eq:  (term,term) -> prop
    neg: prop -> prop
    conj: (prop,prop) -> prop
    fa:  (term -> prop) -> prop
    ex:  (term -> prop) -> prop
  }
  
  // ° is dot notation for low-binding application
  example = (t:FOL.term) -> FOL{fa ° x -> eq(x, `t`)}

  // However, pattern-matching on quotations with bound variables requires inductive functions that can recurse into open terms, which is not supported yet.

  test = test1 & test2

}