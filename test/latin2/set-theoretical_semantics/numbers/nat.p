module set_sem_nat {
    theory NatZF {
        include .nats.Nats
        include .set_sem_sfol.TypedUniversalQuantificationNDSet
        include .sfol.SFOLEQND
    }

    theory NatPlusZF {
        include NatZF
    }
}