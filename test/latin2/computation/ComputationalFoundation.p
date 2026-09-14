module ComputationalFoundation {
    theory CF {
        include .nat.NatPlusTimes
        include .mutability.MutableVariables
        include .IO.IOOps
        include .ifte_computation.IfteOps
        include .sequences.SequencingOps
        include .recursable_definitions.RecurseableDefinitions
        include .loops.WhileOps
        include .exceptions.Exceptions
        include .theoriesAsClasses.TheoriesAsClasses
        include .ContainerTypes.ListComputation
        include .Options.UnsafeOptions
    }

    theory Counter {
        include CF
    }

    theory Program {
        include CF
        include .booleans.TrueFalse
    }
}
