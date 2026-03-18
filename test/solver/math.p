
module Math {

    // Constants
    PI : float
    E : float

    // abs, sign
    abs = (x:float) -> {if (x>=0) x else -x}
    sign = (x:float) -> {if (x==0) 0 else if (x>0) 1 else -1}

    // round
    round : float -> int
    //round = (x:float) -> {}
    floor : float -> float
    //floor = (x:float) -> {}
    ceil : float -> float
    //ceil = (x:float) -> {}

    // trigonometry
    sin : float -> float
    //sin = (x:float) -> {???}
    asin : float -> float
    //asin = (x:float) -> {}

    //cos = (x:float) -> {???}
    cos : float -> float
    acos : float -> float
    //acos = (x:float) -> {}

    //tan = (x:float) -> {???}
    tan : float -> float
    atan : float -> float
    //atan = (x:float) -> {}
    // JS Math atan2 --> atan of y/x ----> [-PI, PI]
    //atan2 = (y:float, x:float) -> {}

    sinh : float -> float
    cosh : float -> float
    tanh : float -> float
    //sinh = (x:float) -> {}
    //cosh = (x:float) -> {}
    //tanh = (x:float) -> {}

    // exp, log
    exp = (x:float) -> {E^x}
    pow = (b:float, x:float) -> {b^x}
    pow2 = (b:float) -> {return b*b}

    ln : float -> float
    log10 : float -> float
    log2 : float -> float
    log : (float, float) -> float
    //ln = (x:float) -> {}
    //log10 = (x:float) -> {}
    //log2 = (x:float) -> {}
    //log = (x: float, b: float) -> {}

    // sqrt
    sqrt : float -> float
    cbrt : float -> float
    //sqrt = (x:float) -> {}
    //cbrt = (x:float) -> {}

    // min, max
    __helper_minmax : (x:float,ns:[float],min:bool)->float
    __helper_minmax = (x:float,ns:[float],min:bool) -> {
        ns match {
            [] -> x
            hd -: r -> if ((hd<x)==min) __helper_minmax(hd,r,min) else __helper_minmax(x,r,min)
        }
    }
    min = (ns:[float]) -> {
        ns match {
            [] -> ???
            hd -: r -> __helper_minmax(hd, r,true)
        }
    }
    max = (ns:[float]) -> {
        ns match {
            [] -> ???
            hd -: r -> __helper_minmax(hd, r,false)
        }
    }


    // misc
    toDegrees = (r:float) -> { r*180/PI }
    toRadians = (d:float) -> { d*PI/180 }
}

// module math_exact {
//
//    include types
//    type sym
//
//    // constants
//    PI : sym
//    E : sym
//
//    // abs, sign
//    abs = (x:sym) -> {}
//    sign = (x:sym) -> {}
//
//    // ASK round
//    round = (x:sym) -> {}
//    floor = (x:sym) -> {}
//    ceil = (x:sym) -> {}
//
//    // exp
//    pow2 = (b:sym) -> {}
//    
//    // toFloat
//    toFloat = (x:sym) -> {}
//
//    // trigonometry
//    sin = (x:sym) -> {}
//    asin = (x:sym) -> {}
//    cos = (x:sym) -> {}
//    acos = (x:sym) -> {}
//    tan = (x:sym) -> {}
//    atan = (x:sym) -> {}
//    atan2 = (y:sym, x:sym) -> {}
//    sinh = (x:sym) -> {}
//    cosh = (x:sym) -> {}
//    tanh = (x:sym) -> {}
//
//    // exp, log
//    // exp sometime exact, if e in N
//    exp = (x:sym) -> {}
//    log = (x:sym) -> {}
//    log10 = (x:sym) -> {}
//    log2 = (x:sym) -> {}
//    pow = (b:sym, e:sym) -> {}
//
//
//    // Axiome
//    // ASK ??
//    //sinPI : |- sin(PI) == 0
//}