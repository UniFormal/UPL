module relevant {
    theory AxiomIdentity {
        include .pl.Implication
    }

    theory AxiomPrefixing {
        include .pl.Implication
    }

    theory AxiomSuffixing {
        include .pl.Implication
    }

    theory AxiomContraction {
        include .pl.Implication
    }

    theory RelevantT {
        include .pl.ImplicationNDE
        include AxiomIdentity
        include AxiomPrefixing
        include AxiomSuffixing
        include AxiomContraction
    }

    theory RuleTransitivity {
        include .pl.Implication
        include .concepts.Proofs
    }

    theory RulePrefixing {
        include .pl.Implication
        include .concepts.Proofs
    }

    theory RuleSuffixing {
        include .pl.Implication
        include .concepts.Proofs
    }

    theory RelevantS {
        include AxiomPrefixing
        include AxiomSuffixing
        include RuleTransitivity
        include RulePrefixing
        include RuleSuffixing
    }

    theory AxiomEntT {
        include .pl.Implication
    }

    theory DisjunctionAsConjunction {
        include .pl.Conjunction
        include .pl.Negation
    }

    theory EquivalenceAsImplication {
        include .pl.Implication
        include .pl.Conjunction
    }

    theory AxiomConjunctionElimination {
        include .pl.Implication
        include .pl.Conjunction
    }

    theory AxiomDisjunctionIntroduction {
        include .pl.Implication
        include DisjunctionAsConjunction
    }

    theory AxiomConjunctionIntroduction {
        include .pl.Implication
        include .pl.Conjunction
    }

    theory AxiomDisjunctionElimination {
        include DisjunctionAsConjunction
        include EquivalenceAsImplication
    }

    theory AxiomDistribution {
        include DisjunctionAsConjunction
        include .pl.Implication
    }

    theory AxiomContraposition {
        include .pl.Implication
        include .pl.Negation
    }

    theory AxiomDoubleNegation {
        include .pl.Implication
        include .pl.Negation
    }

    theory RelevantE {
        include AxiomIdentity
        include AxiomEntT
        include AxiomSuffixing
        include AxiomContraction
        include AxiomConjunctionElimination
        include AxiomDisjunctionIntroduction
        include AxiomConjunctionIntroduction
        include AxiomDisjunctionElimination
        include AxiomDistribution
        include AxiomContraposition
        include AxiomDoubleNegation
        include .pl.ImplicationNDE
        include .pl.ConjunctionNDI
    }

    theory AxiomAssertion {
        include .pl.Implication
    }

    theory RelevantR {
        include AxiomIdentity
        include AxiomAssertion
        include AxiomSuffixing
        include AxiomContraction
        include AxiomConjunctionElimination
        include AxiomDisjunctionIntroduction
        include AxiomConjunctionIntroduction
        include AxiomDisjunctionElimination
        include AxiomDistribution
        include AxiomContraposition
        include AxiomDoubleNegation
        include .pl.ImplicationNDE
        include .pl.ConjunctionNDI
    }

    theory AxiomK {
        include .modal.Box
        include .pl.Implication
    }

    theory AxiomKAnd {
        include .modal.Box
        include .pl.Implication
        include .pl.Conjunction
    }

    theory RuleNecessitation {
        include .modal.Box
        include .concepts.Proofs
    }

    theory RelevantNR {
        include RelevantR
        include AxiomK
        include AxiomKAnd
        include RuleNecessitation
    }
}
