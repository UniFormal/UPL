module Test {
    theory A {
      a: int = 10
    }

    // Adding declarations to an instance is not supported in the core fragment (for now)
    inst = A { b = 3 }

    test = inst.b
}