module subtyping {
    theory Subtyping {
        include .concepts.Types
        include .concepts.Logic
        subtype: (tp, tp) -> prop # infix ⪽
    }

    theory SubtypingPreorder {
        include Subtyping
        sub: .relations.Preorder {
            type carrier = tp, 
            rel = (A, B) -> ⊦A⪽B
        }
    }

    theory SoftSubtyping {
        include .concepts.SoftTypedTerms
        include Subtyping
        subtypeI:--- (forall x. ⊦x∶A => ⊦x∶B) => ⊦A⪽B
        subtypeE:--- ⊦A⪽B => forall x. ⊦x∶A => ⊦x∶B

        realize SubtypingPreorder
        subreal = sub {
            refl = ???
            trans = ???
        }
    }

    theory HardSubtyping {
        include .concepts.TypedTerms
        include .equality.TypedEquality

        include Subtyping
        include SubtypingPreorder

        inject: (A, B, dedT A⪽B, tm A) -> tm B
        inject_irrelevant:--- tequal(B, inject(A, B, p, x), x) 
        inject_refl:--- tequal(A, inject(A, B, sub.refl, x), x) 
        inject_trans:--- tequal(C, inject(B, C, Q, inject(A, B, P, x)), inject(A, C, P, x)) 
    }
}