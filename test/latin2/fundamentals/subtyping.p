module subtyping {
    theory Subtyping {
        include .concepts.Types
        include .concepts.Logic
        subtype: (tp, tp) -> prop # infix ⪽
    }

    theory SubtypingPreorder {
        include Subtyping
        sub: .relations.Preorder {
            type univ = tp, 
            rel = (A, B) -> ⊦(A ⪽ B)
        }
    }

    theory SoftSubtyping {
        include .concepts.SoftTypedTerms
        include Subtyping
        subtypeI:--- (forall X. ⊦of(X,A) => ⊦of(X,B)) => ⊦(A ⪽ B)
        subtypeE:--- ⊦(A ⪽ B) => forall X. ⊦of(X,A) => ⊦of(X,B)

        // is this correct?
        realize SubtypingPreorder
        subReal = sub {
            refl = ???
            trans = ???
        }
    }

    theory HardSubtyping {
        include .concepts.TypedTerms
        include .equality.TypedEquality

        include Subtyping
        include SubtypingPreorder

        // don't know how to do this
        inject: ???
        inject_irrelevant: ???
        inject_refl: ???
        inject_trans: ???
    }
}