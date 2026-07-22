theory meta_divgroups {
    theory DivGroup {
        include .relations.Carrier
        e : univ
        div: (univ, univ) -> univ
        self_div:--- div(x, x) == e
        unit_neutR:--- div(x, e) == x
        reciprocal:--- div(e, div(x, y)) == div(y, x) 
        reduce:--- div(div(x, z), div(y, z)) == div(x, y)
    }
}