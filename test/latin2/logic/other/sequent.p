module sequent {
    theory Contexts {
        include .concepts.Propositions
    }

    theory ContextMap {
        include Contexts
    }

    theory ContextFold {
        include Contexts
    }

    theory SequentProofs {
        include Contexts
    }

    theory SequentBase {
        include SequentProofs
    }

    theory InContext {
        include SequentBase
    }

    // Structural Rules -------------------------------------------------------------------
    theory Cut {
        include SequentProofs
    }

    theory Weakening {
        include SequentProofs
    }

    theory Contraction {
        include SequentProofs
    }

    theory Exchange {
    }

    // Truth -------------------------------------------------------------------
    theory SequentTruthLeft {
        include SequentProofs
        include .pl.Truth
    }

    theory SequentTruthRight {
        include SequentProofs
        include .pl.Truth
    }

    theory SequentTruthRightWeakened {
        include SequentProofs
        include .pl.Truth
    }

    theory SequentTruth {
        include SequentTruthLeft
        include SequentTruthRight
    }

    // Falsity -------------------------------------------------------------------
    theory SequentFalsityLeft {
        include SequentProofs
        include .pl.Falsity
    }

    theory SequentFalsityRight {
        include SequentProofs
        include .pl.Falsity
    }

    theory SequentFalsity {
        include SequentFalsityLeft
        include SequentFalsityRight
    }

    // Negation -------------------------------------------------------------------
    theory SequentNegationLeft {
        include SequentProofs
        include .pl.Negation
    }

    theory SequentNegationRight {
        include SequentProofs
        include .pl.Negation
    }

    theory SequentNegation {
        include SequentNegationLeft
        include SequentNegationRight
    }

    // Conjunction -------------------------------------------------------------------
    theory SequentConjunctionLeft {
        include SequentProofs
        include .pl.Conjunction
    }

    theory SequentConjunctionRightSimple {
        include SequentProofs
        include .pl.Conjunction
    }

    theory SequentConjunctionRightCompositional {
        include SequentProofs
        include .pl.Conjunction
    }

    theory SequentConjunctionSimple {
        include SequentConjunctionLeft
        include SequentConjunctionRightSimple
    }

    theory SequentConjunctionCompositional {
        include SequentConjunctionLeft
        include SequentConjunctionRightCompositional
    }

    theory SequentConjunction {
        include SequentConjunctionLeft
        include SequentConjunctionRightSimple
        include SequentConjunctionRightCompositional
    }

    // Disjunction -------------------------------------------------------------------
    theory SequentDisjunctionLeftSimple {
        include SequentProofs
        include .pl.Disjunction
    }

    theory SequentDisjunctionLeftCompositional {
        include SequentProofs
        include .pl.Disjunction
    }

    theory SequentDisjunctionRight {
        include SequentProofs
        include .pl.Disjunction
    }

    theory SequentDisjunctionSimple {
        include SequentDisjunctionLeftSimple
        include SequentDisjunctionRight
    }

    theory SequentDisjunctionCompositional {
        include SequentDisjunctionLeftCompositional
        include SequentDisjunctionRight
    }

    theory SequentImplication {
        include SequentProofs
        include .pl.Implication
    }

    theory SequentExample {
        include SequentConjunction
        include SequentImplication
        // include Weakening
        include Exchange
        include InContext
    }

    theory SequentUniversalQuantification {
        include SequentProofs
        include .fol.UniversalQuantification
    }

    theory SequentExistentialQuantification {
        include SequentProofs
        include .fol.ExistentialQuantification
    }

    theory SequentBigConjunction {
        include ContextFold
        include .pl.Conjunction
        include .pl.Truth
    }

    theory SequentBigDisjunction {
        include ContextFold
        include .pl.Disjunction
        include .pl.Falsity
    }

    theory SequentAsND {
        include SequentBigConjunction
        include SequentBigDisjunction
        include .pl.Implication
        include .concepts.Proofs
    }
}
