module refutation {
    theory AntiseqAxiom {
    }

    theory Antisequent {
        include .sequent.Contexts
        include AntiseqAxiom
    }

    theory RefutationNegationLeft {
        include Antisequent
        include .pl.Negation
    }

    theory RefutationNegationRight {
        include Antisequent
        include .pl.Negation
    }

    theory RefutationConjunctionLeft {
        include Antisequent
        include .pl.Conjunction
    }

    theory RefutationConjunctionRight {
        include Antisequent
        include .pl.Conjunction
    }

    theory RefutationDisjunctionLeft {
        include Antisequent
        include .pl.Disjunction
    }

    theory RefutationDisjunctionRight {
        include Antisequent
        include .pl.Disjunction
    }

    theory RefutationImplication {
        include Antisequent
        include .pl.Implication
    }

    theory PLRefutation {
        include RefutationNegationLeft
        include RefutationNegationRight
        include RefutationConjunctionLeft
        include RefutationConjunctionRight
        include RefutationDisjunctionLeft
        include RefutationDisjunctionRight
        include RefutationImplication
        include .sequent.Weakening
        include .sequent.Contraction
        include .sequent.Exchange
    }
}
