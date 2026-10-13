module unit_type {
    theory UnitType {
        include .equality.TypedEqualityND
        unitType: tp
        unit: tm unitType
        unitArrow: A -> tm A -> tm unitType = A -> a -> unit

        unitUnique: u -> ded tequal(unitType, u, unit)
        unitUniversal: (A,B,F:tm A -> tm B, a) -> ded tequal(unitType, unitArrow B (F a), unitArrow A a)
    }
}