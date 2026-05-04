module hom {
    theory HomMagma {
        M : .magmas.Magma
        N : .magmas.Magma
        h : M -> N
        isHom:--- h(x∘y) == h(x)∘h(y)
    }

    // pretty sure this is wrong. how to do it right?
    theory HomSemigroup {
        include HomMagma
        M : .magmas.Semigroup
        N : .magmas.Semigroup
    }
}