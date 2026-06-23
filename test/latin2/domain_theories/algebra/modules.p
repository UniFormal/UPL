module modules {
    theory Scalars {
        scalars: .relations.Carrier
    }

    theory RingScalars {
        include Scalars
        scalars: .ringoids.Ring
    }

    theory SkewFieldScalars {
        include Scalars
        scalars: .ringoids.SkewField 

    }

    theory FieldScalars {
        include Scalars
        scalars: .ringoids.Field 
    }

    theory LeftModule {
        include Scalars
        include .groups.CommGroup
        left_scalars: RingScalars

        left_scalar_mult: (scalars.univ, univ) -> univ # infix ⋅
        left_identity:--- (left_scalars.scalars.mult.e) ⋅ x == x
        left_distrib_scalars:--- (left_scalars.scalars.add.op(s1,s2)) ⋅ x == (s1 ⋅ x) ∘ (s2 ⋅ x)
        left_distrib_vectors:--- s ⋅ (x ∘ y) == (s ⋅ x) ∘ (s ⋅ y) 
        left_assoc:--- left_scalars.scalars.mult.op(s1, s2) ⋅ x == s1 ⋅ (s2 ⋅ x) 
    }

    theory RightModule {
        include RingScalars
        include .groups.CommGroup
        right_scalars: RingScalars

        right_scalar_mult: (univ, scalars.univ) -> univ # infix ⋅
        right_identity:--- x ⋅ (right_scalars.scalars.mult.e) == x
        right_distrib_scalars:--- x ⋅ (right_scalars.scalars.add.op(s1,s2)) == (x ⋅ s1) ∘ (x ⋅ s2)
        right_distrib_vectors:--- (x ∘ y) ⋅ s == (x ⋅ s) ∘ (y ⋅ s)
        right_assoc:--- x ⋅ right_scalars.scalars.mult.op(s1, s2) == (x ⋅ s1) ⋅ s2
    }

    theory BiModule {
        include LeftModule
        include RightModule
    }

    theory LeftVectorSpace {
        include LeftModule
        left_scalars: SkewFieldScalars
    }

    theory RightVectorSpace {
        include RightModule
        right_scalars: SkewFieldScalars
    }

    theory VectorSpace {
        include LeftModule
        left_scalars: FieldScalars
    }
}