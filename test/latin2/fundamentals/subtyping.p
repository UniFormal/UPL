module subtyping {
    theory Subtyping {
        include .concepts.Types
        include .concepts.Logic

        subtype: (tp, tp) -> prop # infix ⪽
    }

    theory SoftSubtyping {
        include .concepts.SoftTypedTerms
        include Subtyping

        subtypeI:--- (forall X. ⊦of(X,A) => ⊦of(X,B)) => ⊦(A ⪽ B)
        subtypeE:--- ⊦(A ⪽ B) => forall X. ⊦of(X,A) => ⊦of(X,B)
    }
}