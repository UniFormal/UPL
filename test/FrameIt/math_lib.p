
module types {
    type float = int
}

module math_float {

    include types

    // Constants
    PI : float
    E : float

    // abs, sign
    abs = (x:float) -> {}
    sign = (x:float) -> {}

    // round
    round = (x:float) -> {}
    floor = (x:float) -> {}
    ceil = (x:float) -> {}

    // trigonometry
    sin = (x:float) -> {}
    asin = (x:float) -> {}

    cos = (x:float) -> {}
    acos = (x:float) -> {}

    tan = (x:float) -> {}
    atan = (x:float) -> {}
    // JS Math atan2 --> atan of y/x ----> [-PI, PI]
    atan2 = (y:float, x:float) -> {}

    sinh = (x:float) -> {}
    cosh = (x:float) -> {}
    tanh = (x:float) -> {}

    // exp, log
    exp = (x:float) -> {}
    log = (x:float) -> {}
    log10 = (x:float) -> {}
    log2 = (x:float) -> {}
    pow = (b:float, e:float) -> {}
    pow2 = (b:float) -> {return b*b}

    // sqrt
    sqrt = (x:float) -> {}
    cbrt = (x:float) -> {}

    // min, max
    // ASK how more arguments?
    //min = (a:float, b:float) -> {}
    //max = (a:float, b:float) -> {}

    // misc
    toDegrees = (r:float) -> {}
    toRadians = (d:float) -> {}
}

module math_exact {

    include types
    type sym

    // constants
    PI : sym
    E : sym

    // abs, sign
    abs = (x:sym) -> {}
    sign = (x:sym) -> {}

    // ASK round
    round = (x:sym) -> {}
    floor = (x:sym) -> {}
    ceil = (x:sym) -> {}

    // exp
    pow2 = (b:sym) -> {}
    
    // toFloat
    toFloat = (x:sym) -> {}

    // trigonometry
    sin = (x:sym) -> {}
    asin = (x:sym) -> {}
    cos = (x:sym) -> {}
    acos = (x:sym) -> {}
    tan = (x:sym) -> {}
    atan = (x:sym) -> {}
    atan2 = (y:sym, x:sym) -> {}
    sinh = (x:sym) -> {}
    cosh = (x:sym) -> {}
    tanh = (x:sym) -> {}

    // exp, log
    // exp sometime exact, if e in N
    exp = (x:sym) -> {}
    log = (x:sym) -> {}
    log10 = (x:sym) -> {}
    log2 = (x:sym) -> {}
    pow = (b:sym, e:sym) -> {}


    // Axiome
    // ASK ??
    //sinPI : |- sin(PI) == 0
}