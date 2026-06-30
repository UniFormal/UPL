module subtyping {
    theory Subtyping {
        include .concepts.Types
        include .concepts.Logic
        subtype: (tp, tp) -> prop # infix ⪽
    }

    theory SubtypingPreorder {
        include Subtyping

        sub: .relations.Preorder {
            type carrier = tp
            // doesn't work 
            // type rel(c1:carrier, c2:carrier) = ded c1⪽c2
            refl = ???
            trans = ???
        }
    }

    theory SoftSubtyping {
        include .concepts.SoftTypedTerms
        include Subtyping
        subtypeI: (A,B) -> (x -> ded x∶A -> ded x∶B) -> ded A⪽B
        subtypeE: (A,B) -> ded A⪽B -> x -> ded x∶A -> ded x∶B

        // realize SubtypingPreorder
        // sub = .relations.Preorder {
        //     refl = ???
        //     trans = ???
        // }
    }

    theory HardSubtyping {
        include .concepts.TypedTerms
        include .equality.TypedEquality

        include Subtyping
        include SubtypingPreorder

        inject: (A, B, ded A⪽B, tm A) -> tm B
        inject_irrelevant: (A,x,p) -> ded tequal(A, inject(A, A, p, x), x) 
        // missing parts ugly without implicit args
        inject_refl: (A,x) -> ded tequal(A, inject(A, A, ???, x), x) 
        inject_trans: (A,B,C,x,P,Q) -> ded tequal(C, inject(B, C, Q, inject(A, B, P, x)), inject(A, C, ???, x)) 
    }
}