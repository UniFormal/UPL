module lists {
  theory ListOperations {
      include .collection_types.Lists
  }

  theory ListZip {
      include ListOperations
      include .product_types.SimpleProducts
  }
}
