module Test {
    theory A {
      a: int = 10
    }

    inst = A { b = 3 }

    test = inst.b
}