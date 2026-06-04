theory divgroups {
    theory DivGroup {
        include .relations.Carrier
        e : univ
        div: (univ, univ) -> univ
        self_div:--- div(x, x) == e
        unit_neutR:--- div(e, div(x, y)) == div(y, x) 
    }
}