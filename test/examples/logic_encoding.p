module Logic {

  // needed: parameters of type yields dependent types; parameters of terms are implicit arguments

  theory FOL {
     type term
     type prop

     conj: (prop,prop) -> prop # infix ∧
     neg: prop -> prop  # prefix ¬ 
     all: (term -> prop) -> prop # bindfix ∀
     equal: (term,term) -> prop # infix ≐

     thm: prop -> bool # prefix ⊦
     contra = forall F. thm(F)

     conjI:  |- forall F,G. ⊦F & ⊦G => ⊦(F∧G)
     conjEl: |- forall F,G. ⊦(F∧G) => ⊦F
     conjEr: |- forall F,G. ⊦(F∧G) => ⊦G

     negI: |- forall F. (⊦F => contra) => ⊦ ¬F
     negE: |- forall F. ⊦ ¬F => ⊦F => contra

     allI: |- forall F. (forall X. ⊦F(X)) => ⊦all(F)
     allE: |- forall F. ⊦all(F) => forall X. ⊦F(X)

     eqI: |- forall X. ⊦(X≐X)
     eqE: |- forall X,Y. ⊦(X≐Y) => forall P. ⊦P(X) => ⊦P(Y)
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