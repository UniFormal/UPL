// This file defines a number of alternative base languages for language features.
//
// Typically,
// - every language extends exactly one of them
// - every language feature can be defined relative to all or at least multiple of them.

module base_languages {
    // logics without any typing
    // paradigmatic languages: first-order logic
    theory UntypedLogic {
        include .concepts.Logic
        include .concepts.Terms
    }

    // typed logics
    // paradigmatic languages: sorted/typed first-order logic, λ-cube logics
    theory TypedLogic {
        include .concepts.Logic
        include .concepts.TypedTerms
    }

    // logics with flexible type systems
    // paradigmatic languages: mathematics (arguably)
    theory SoftTypedLogic {
        include .concepts.Logic
        include .concepts.SoftTypedTerms
    }

    // logics whose propositions are terms
    // paradigmatic languages: higher-order logic
    theory InternalLogic {
        include .concepts.InternalPropositions
        include .concepts.Proofs
    }

    // logics whose types are terms
    // paradigmatic languages: set theory
    theory InternallyTypedLogic {
        include .concepts.InternalTypes
        include .concepts.Logic
    }
}