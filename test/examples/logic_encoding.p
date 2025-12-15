module Logic {

  // needed: parameters of type yields dependent types; parameters of terms are implicit arguments

  theory FOL {
     type term
     type prop

     conj: (prop,prop) -> prop
     neg: prop -> prop
     all: (term -> prop) -> prop
     equal: (term,term) -> prop

     thm: prop -> bool
     contra = forall F. thm(F)

     conjI:  |- forall F,G. thm(F) & thm(G) => thm(conj(F,G))
     conjEl: |- forall F,G. thm(conj(F,G)) => thm(F)
     conjEr: |- forall F,G. thm(conj(F,G)) => thm(G)

     negI: |- forall F. (thm(F) => contra) => thm(neg(F))
     negE: |- forall F. thm(neg(F)) => thm(F) => contra

     allI: |- forall F. (forall X. thm(F(X))) => thm(all(F))
     allE: |- forall F. thm(all(F)) => forall X. thm(F(X))

     eqI: |- forall X. thm(equal(X,X))
     eqE: |- forall X,Y. thm(equal(X,Y)) => forall P. thm(P(X)) => thm(P(Y))
  }

  theory Nat {
    include FOL
    zero: term
    succ: term -> term
    plus: (term,term) -> term
    plus_zero: |- forall x. thm(equal(plus(x,zero), x))
    plus_succ: |- forall x,n. thm(equal(plus(x,succ(n)), succ(plus(x,n))))
  }
}