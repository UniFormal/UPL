module additive {
    theory Carrier {
        type univ
    }

    theory Magma {
        include Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory Commutative {
        include Magma
        comm:--- x∘y == y∘x
    }

    theory Idempotent {
        include Magma
        idem:--- x∘x == x
    }

    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
    }

//-------------------------------------------------------

    theory AdditiveMagma {
        include Carrier
        add: (univ,univ) -> univ # infix +
        magma = Magma {type univ = ..univ, op = add}
    }
    fromMagma(m: Magma) = AdditiveMagma {type univ = m.univ, add = m.op}

    // theory AdditiveCommutative {
    //     include AdditiveMagma
    //     add_comm:--- x+y == y+x
    // }

    // theory AdditiveIdempotent {
    //     include AdditiveMagma
    //     idem:--- x+x == x
    // }

    // theory AdditiveSemigroup {
    //     include AdditiveMagma
    //     assoc:--- x+(y+z) == (x+y)+z
    // }

}