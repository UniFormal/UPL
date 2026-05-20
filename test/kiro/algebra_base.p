module algebra_base {
      theory Carrier {
        type univ
    }
    theory Relation {
        include Carrier
        rel: (univ,univ) -> bool # infix %  // # declares notation
    }
    theory Reflexive {
        include Relation
        refl:--- x % x  // :--- abbreviates axiom for universal closure
    }
    theory Transitive {
        include Relation
        trans:--- x%y & y%z => x%z
    }
    theory Symmetric {
        include Relation
        sym:--- x%y => y%x
    }
    theory Preorder {
        include Reflexive
        include Transitive
    }
    theory PER {
        include Symmetric
        include Transitive
    }
    theory Equivalence {
        include PER
        include Preorder
    }
    theory Magma {
        include Carrier
        op: (univ,univ) -> univ # infix ∘
    }
    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
    }
    theory Abelian {
        include Magma
        comm:--- x∘y == y∘x
    }
    theory Pointed {
        include Magma
        e: univ
    }
    theory Monoid {
        include Pointed
        include Semigroup
        neutL:--- e∘x==x
        neutR:--- x∘e==x
    }
    theory Idempotent {
        include Magma
        idem:--- x∘x==x
    }
    theory Band{
        include Semigroup
        include Idempotent
    }
    theory Semilattice {
        include Abelian
        include Band
    }
    theory BoundedSemilattice {
        include Semilattice
        include Monoid
    }
    theory Group {
        include Monoid
        inv: univ -> univ # postfix ⁻
        invL:--- x∘x⁻ == e
        invR:--- x⁻ ∘ x == e
    }
    theory SubGroup {
        include Group
        per: PER {type univ = ..univ}
        perapply # infix % = per.rel
        e_per:--- e % e
        op_per:--- x1 % y1 & x2 % y2 => (x1∘y1) % (x2∘y2)
        inv_per:--- x % y => x⁻ % y⁻
    }
    theory AbelianGroup {
        include Group
        include Abelian
    }

    // for theory H:
    // H {d1, ...} abbreviates {include H, d1, ...}
    theory BiMagma {
        include Carrier
        // add must be a model of {type univ == ..univ, op: (univ,univ) -> univ}
        add  : Magma {type univ = ..univ} // .. accesses surrounding theory
        mult : Magma {type univ = ..univ}
    }

    theory Ringoid {
        include BiMagma
        // Distributivity axioms
        distL:--- mult.op(x, add.op(y, z)) == add.op(mult.op(x, y), mult.op(x, z))
        distR:--- mult.op(add.op(x, y), z) == add.op(mult.op(x, z), mult.op(y, z))
    }

    theory BiMonoid {
        include Ringoid
        add : Monoid
        mult : Monoid
    }

    theory Semiring {
        include BiMonoid
        add: Abelian
    }

    theory Rng {
        include Ringoid
        add:  AbelianGroup
        mult: Semigroup
    }
    theory Ring {
        include Rng
        mult: Monoid
    }
    theory AbelianRing {
        include Ring
        mult: Abelian
    }

    theory SemiField {
        include Ring
        // Redefine mult as a Monoid with inverse, but with conditional axioms
        // mult: Monoid {
        //     type univ = ..univ
        //     inv: univ -> univ
        //     invL:--- (x != add.e) => op(x, inv(x)) == e
        //     invR:--- (x != add.e) => op(inv(x), x) == e
        // }
        mult: Group
    }

    theory Field {
        include SemiField
        mult: Abelian
    }

    theory VectorSpace {
        // A vector space requires:
        // 1. A field F (scalars)
        // 2. An abelian group V (vectors)
        // 3. Scalar multiplication operation
        // 4. Compatibility axioms
        
        field: Field // The scalar field
        
        // Vector addition forms an abelian group
        vectors: AbelianGroup
        
        // Scalar multiplication: F × V → V
        scalarMult: (field, vectors) -> vectors
        
        // Compatibility axioms for scalar multiplication
        
        // 1. Compatibility with field multiplication
        compat:--- scalarMult(a, scalarMult(b, v)) == scalarMult(field.mult.op(a, b), v)
        
        // 2. Identity element of scalar field acts as identity
        identity:--- scalarMult(field.mult.e, v) == v
        
        // 3. Distributivity of scalar multiplication with respect to vector addition
        distVec:--- scalarMult(a, vectors.op(u, v)) == vectors.op(scalarMult(a, u), scalarMult(a, v))
        
        // 4. Distributivity of scalar multiplication with respect to field addition
        distScalar:--- scalarMult(field.add.op(a, b), v) == vectors.op(scalarMult(a, v), scalarMult(b, v))
    }
}