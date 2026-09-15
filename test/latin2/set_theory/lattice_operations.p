module lattice_operations {
    theory Union {
        include .setbase.SetBase
    }

    theory UnionEmpty {
        include Union
        include .finite_sets.EmptySet
    }

    theory Intersection {
        include .setbase.SetBase
    }

    theory IntersectionEmpty {
        include Intersection
        include .finite_sets.EmptySet
    }

    theory BigUnion {
        include .setbase.SetBase
    }

    theory BigIntersection {
        include .setbase.SetBase
        include .setbase.EmptyDefinitions
    }

    theory Difference {
        include .setbase.SetBase
    }

    theory DifferenceEmpty {
        include Difference
        include .finite_sets.EmptySet
    }

    theory DifferenceIntersection {
        include Difference
        include Intersection
        include .finite_sets.EmptySet
    }

    theory Complement {
        include .setbase.SetBase
    }

    theory ComplementEmpty {
        include Complement
        include .finite_sets.EmptySet
    }

    theory ComplementUnion {
        include Complement
        include Union
    }

    theory ComplementIntersection {
        include Complement
        include Intersection
        include .finite_sets.EmptySet
    }
}
