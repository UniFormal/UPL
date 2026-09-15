module views_cartesian_product {
    // The views currently still need single theories as a domain and codomain, which
    // forces us to provide spurious named theories. This should be refactored when
    // multi-theory domains and codomains are possible.

    // Views for Img
    theory OrderedImageFilter {
        include .cartesian_product.OrderedPairs
        include .operations.Image
        include .operations.Filter
    }

    // ImgOrderedImageFilter: OrderedImageFilter -> .cartesian_product.Img = i -> §{
    //     include .cartesian_product.OrderedPairs
    // }

    // Views for CartesianProduct
    theory OrderedBigUnionImage {
        include .cartesian_product.OrderedPairs
        include .lattice_operations.BigUnion
        include .operations.Image
    }

    // CartImage: OrderedBigUnionImage -> .cartesian_product.CartesianProduct = c -> §{
    //     include .cartesian_product.OrderedPairs
    // }

    // SigmaCart: .cartesian_product.Sigma -> .cartesian_product.CartesianProduct = s -> §{
    //     include .cartesian_product.OrderedPairs
    // }

    // // Views for Sigma
    // SigmaUnion: OrderedBigUnionImage -> .cartesian_product.Sigma = s -> §{
    //     include .cartesian_product.OrderedPairs
    // }

    // SigmaFromMod: .cartesian_product.SigmaMod -> .cartesian_product.Sigma = s -> §{
    //     include .cartesian_product.OrderedPairs
    // }
}
