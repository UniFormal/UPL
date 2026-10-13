module hollight {
    // Representation of HOL Light following http://hol-light.googlecode.com/svn/trunk/fusion.ml
    // @author Cezary Kaliszyk, Florian Rabe

    theory Kernel {
    }

    // The foundation HOL as a theory of HOL Light, see class.ml and nums.ml
    theory HOL {
        include Kernel
    }
}
