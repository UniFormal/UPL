module modules {
    theory Scalars {
    }

    theory RingScalars {
        include Scalars
    }

    theory FieldScalars {
        include Scalars
    }

    theory LeftModule {
        include Scalars
        include .ringoids.Ring
    }

    theory RightModule {
        include .groups.CommGroup
    }

    theory BiModule {
        include LeftModule
        include RightModule
    }

    theory VectorSpace {
        include LeftModule
    }
}
