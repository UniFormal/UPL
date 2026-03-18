module Test022 {

    s1: set[int] = set[1,2,3]
    s2: set[int] = set[1,2,3,3]

    // problem, related to checking and type conversion; maybe solved by compiling checked code (currently only parsed)
    s3: set[int] = [1,2,3]
    s4: set[int] = [1,2,3,3]

    s5 = set[1,2,3]

    // what about set union, set comprehension, and ranges n..m in UPL?


}