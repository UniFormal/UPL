module base_languages {
    theory UntypedLogic {
        include .concepts.Logic
        include .concepts.Terms
    }

    theory TypedLogic {
        include .concepts.Logic
        include .concepts.TypedTerms
    }

    theory SoftTypedLogic {
        include .concepts.Logic
        include .concepts.SoftTypedTerms
    }
}