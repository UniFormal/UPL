module undefinedness {
    theory UndefinedTerms {
        include .base_languages.UntypedLogic
        udefined: term -> prop
        ustrict_equal: term -> term -> prop
    }

    theory UndefinedTypedTerms {
        include .base_languages.TypedLogic
        tdefined: (A) -> tm A -> prop
        tstrict_equal: (A) -> tm A -> tm A -> prop
    }

    theory UndefinedSoftTypedTerms {
        include .concepts.SoftTypedTerms
        rdefined: term -> tp -> prop
        rstrict_equal: tp -> term -> term -> prop
    }
}