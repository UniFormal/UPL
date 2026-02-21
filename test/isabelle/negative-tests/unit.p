module Unit {

    // unit type
    // parse and check
    u: () = ()
    fu: () -> ()
    fu1: () -> () = x -> x
    fu2: () -> () = x -> ()

    // produces type-checking error
    fu3: () -> () = () -> ()


}