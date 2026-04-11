module Magmas {
    theory Magma {
        include .relations.Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory SubMagma {
        include .relations.SubCarrier
        include Magma
        op_rel:--- x1 % y1 & x2 % y2 => (x1∘y1) % (x2∘y2)
    }

    
}