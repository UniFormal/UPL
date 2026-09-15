module setbase {
    theory SetDefinitions {
    }

    theory ExtensionalityAx {
        include SetDefinitions
    }

    theory SubsetDefinitions {
        include SetDefinitions
    }

    // This could be written in SubsetDefinitions, but then subset would be dependent
    // on ExtensionalityAx. Because both theories are part of SetBase, this would be irrelevant.
    theory SubsetExtensionality {
        include SubsetDefinitions
        include ExtensionalityAx
    }

    theory EmptyDefinitions {
        include SetDefinitions
    }

    theory DisjointDefinitions {
        include SetDefinitions
    }

    theory RelationDefinitions {
        include SetDefinitions
    }

    theory SetBase {
        include SetDefinitions
        include ExtensionalityAx
        include SubsetDefinitions
        // UniverseNonEmpty is used instead of ExistenceAx
        include .nonempty.UniverseNonEmpty
    }
}
