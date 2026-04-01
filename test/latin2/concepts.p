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

   theory SoftTypedTerms {
        include Terms
        include Types
        include Propositions

        of: (term, tp) -> prop
    }

    theory Booleans {
        include Types
        boolean: tp
    }

    // don't know how to do without dependent types

    // theory InternalPropositions {
    //     include Booleans
    //     realize Propositions
    //     prop = tm(boolean)
    // }

    // don't know how to do without dependent types
    // theory TypesAsPredicates {
    //     include Terms
    //     include Propositions
    //     include Logic // Is this needed?

    //     // This doesn't work

    //     // realize SoftTypedTerms
    //     // tp = term -> prop
    //     // of = (X, A) -> A(X)

    //     // don't know if right
    //     tp: term -> prop
    //     of: (term, (term -> prop)) -> prop = (X, A) -> A(X)
    // }

    // don't know how to do without dependent types

    // theory InternalTypes {
    //     include .concepts.Terms
    //     include .concepts.Propositions

    //     iin: term -> term -> prop
    //     realize SoftTypedTerms
    //     tp = term
    //     of = iin
    // }
}