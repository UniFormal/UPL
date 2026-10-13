module quotation {
    theory Strings {
    }

    theory CTTQE {
        include .base_languages.TypedLogic
        include Strings
        include .function_types.SimpleFunctions
        include .undefinedness.UndefinedTypedTerms
    }

    theory Example {
        include CTTQE
    }
}
