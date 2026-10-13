module endofunctors {
  theory TypeOperator {
  }

  theory EndoFunctor {
      include TypeOperator
  }

  // View currently not total, needs Extensionality
  CategoryOfTypes: .function_types.SimpleFunctionsEta -> .category.Category = c -> §{
  }

  theory InternalEndoFunctor {
      include TypeOperator
      include .function_types.SimpleFunctionsEta
  }
}
