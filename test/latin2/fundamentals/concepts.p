module concepts {
    theory Propositions {
        type prop
    }

    theory Proofs {
        include Propositions
        ded: prop -> bool   # prefix ⊦
        lemma:--- ⊦F => (⊦F => ⊦G) => ⊦G
    }

    theory Disproofs {
        include Propositions
        disproof: prop -> bool
    }

    theory Logic {
        include Propositions
        include Proofs

        inconsistent : bool = forall F. ⊦F 
        inconsistentE:--- inconsistent => ⊦F

        realize Disproofs
        disproof = F -> (⊦F => inconsistent)
    }

    theory Terms {
        type term
    }

    theory Types {
        type tp
    }

    theory TypedTerms {
        include Types
        type tm(a: tp)
    }

    theory SoftTypedTerms {
        include Terms
        include Types
        include Propositions

        of: (term, tp) -> prop
    }

    theory Kinds {
        type kd
    }

    theory KindedTypes {
        include Kinds
        type tf(k: kd)
        tpk: kd

        // needs type-valued decrarations
        // realize Types
        // tp = tf(tpk)
    }

    theory Booleans {
        include Types
        boolean: tp
    }

    theory InternalPropositions {
        include Booleans

        // needs type-valued decrarations
        // realize Propositions 
        // prop = tm boolean
    }

    theory TypesAsPredicates {
        include Terms
        include Propositions
        include Logic

        typesAsPredicates : SoftTypedTerms {
            // needs type-valued decrarations
            // tp = term -> prop
            // of = (X, A) -> (A X)
        }
    }

    theory InternalTypes {
        include Terms
        include Propositions

        iin: term -> term -> prop

        // needs type-valued decrarations
        // realize SoftTypedTerms
        // tp = term
        // of = iin
    }
}