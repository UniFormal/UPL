module hom {
    theory HomMagma {
        M : .magmas.Magma
        N : .magmas.Magma
        univ : M -> N
        op:--- univ(x∘y) == univ(x)∘univ(y)
    }

    // pretty sure this is wrong. how to do it right?
    theory HomSemigroup {
        include HomMagma
        M : .magmas.Semigroup
        N : .magmas.Semigroup
    }
}