module set_sem_booleans {
    // Classical booleans
    theory CBooleansZF {
        include .set_sem_fundamentals.TypedEqualitySet
        include .set_sem_nat.NatZF
    }

    theory CBooleanExtensionalityZF {
        include CBooleansZF
    }
}