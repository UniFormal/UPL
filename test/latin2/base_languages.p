module base_languages {
    theory UntypedLogic {
        include .concepts.Logic
        include .concepts.Terms
    }

    theory SoftTypedLogic {
        include .concepts.Logic
        include .concepts.SoftTypedTerms
    }
}