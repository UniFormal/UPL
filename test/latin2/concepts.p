module concepts {
    theory Propositions {
        type prop
    }

    theory Proofs {
        include Propositions
        ded : prop -> bool  # prefix ⊦
        
        lemma:--- ⊦F => (⊦F => ⊦G) => ⊦G
    }

    theory Disproofs {
        include Propositions
        disproof : prop -> bool
    }

    theory Logic {
        include Propositions
        include Proofs

        inconsistent = forall F. ⊦F 
        inconsistentE : inconsistent => forall F. ⊦F

        realize Disproofs
        disproof = forall F. ⊦(F => inconsistent)
    }

    theory Terms {
        type term
    }

    theory Types {
        type tp
    }

    theory TypedTerms {
        include Types
        tm : tp -> bool
    }

    theory SoftTypedTerms {
        include Terms
        include Types
        include Propositions

        of : term -> tp -> prop
    }

    theory Kinds {
        type kd
    }

    theory KindedTypes {
        include Kinds
        tf : kd -> bool
        tpk : kd
        realize Types
        tp = tf(tpk)
    }

    theory Booleans {
        include TypedTerms
        boolean : tp
    }

    theory InternalPropositions {
        include Booleans
        realize Propositions
        prop = tm(boolean)
    }

    theory TypesAsPredicates {
        include Terms
        include Logic

        theory typesAsPredicates{
            include SoftTypedTerms
            include Terms
            include Propositions

            tp = term -> prop
            of = forall X, A. A(X)
        }
    }

    theory InternalTypes {
        include Terms
        include Propositions

        iin : term -> term -> prop
        realize SoftTypedTerms
        tp = term
        of = iin
    }
}