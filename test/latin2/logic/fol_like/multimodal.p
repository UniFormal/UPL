module multimodal {
    theory MultiModal {
        include .concepts.Logic
        type modality
    }

    theory MultiBox {
        include MultiModal
        box: modality -> prop -> prop
    }

    theory MultiDiamond {
        include MultiModal
        diamond: modality -> prop -> prop
    }

    theory MML {
        include MultiModal
        include MultiBox
        include MultiDiamond
    }

    theory SMML {
        include MML
        include .sfol.SFOLEQ
    }
}