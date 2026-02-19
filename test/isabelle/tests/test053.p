module Test053 {

    // the in operator in Isabelle only works for sets
    // need to coerce to type set

    s1 = 1 in set[1,2,3]
    s2 = 1 in list[1,2,3]
    s3 = 1 in bag[1,2,3]

}