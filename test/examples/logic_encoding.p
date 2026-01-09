module Logic {

  // a formalization of first-order logic with natural deduction
  theory FOL {
     // type (non-terminal symbol) for terms
     type term
     // type (non-terminal symbol) for propositions
     type prop

     // connectives (productions) with their types and concrete syntax
     conj:  (prop,prop) -> prop    # infix ∧
     neg:   prop -> prop           # prefix ¬ 
     all:   (term -> prop) -> prop # bindfix ∀
     equal: (term,term) -> prop    # infix ≐

     // even though -> is UPL's function space, higher-order abstract syntax works
     // because we cannot pattern-match on expressions of type term inside the theory

     // the judgment of being a theorem/provable
     // We use Isabelle-style thm: prop -> bool instead of LF-style prf: prop -> type because UPL's support for dependent types is still limited
     // bool, &, =>, and forall are UPL's logic corresponding to LF's type, -->, and Pi
     thm: prop -> bool             # prefix ⊦
     // a property expressing inconsistency: all propositions are theorems
     contra = forall F. ⊦F

     // the ND proof rules for each connective
     // "c :--- F" is syntactic sugar for c: |- Forall F, where
     //   "Forall" takes the universal closure, i.e., it forall-binds all free variables
     //   "|-" forms the type of UPL proofs

     conjI:---  ⊦F & ⊦G => ⊦(F∧G)
     conjEl:--- ⊦(F∧G) => ⊦F
     conjEr:--- Forall ⊦(F∧G) => ⊦G

     negI:--- (⊦F => contra) => ⊦ ¬F
     negE:--- ⊦ ¬F => ⊦F => contra

     allI:--- (forall X. ⊦F(X)) => ⊦ ∀X. F(X)
     allE:--- ⊦ (∀X. F(X)) => forall X. ⊦F(X)

     eqI:--- ⊦(X≐X)
     eqE:--- ⊦(X≐Y) => forall P. ⊦P(X) => ⊦P(Y)
  }

  // an example theory for the natural numbers
  theory Nat {
    include FOL
    zero: term
    succ: term -> term # prefix $
    plus: (term,term) -> term # infix ++
    plus_zero: |- ⊦ ∀x. x ++ zero ≐ x
    plus_succ: |- ⊦ ∀x,n. x ++ $n ≐ $(x++n)
  }
}