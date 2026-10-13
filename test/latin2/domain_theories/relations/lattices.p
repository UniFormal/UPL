module rel_lattices {
  theory LatticeOrder {
      include .rel_orders.Order
      include .rel_orders.Infimum
      include .rel_orders.Supremum
  }

  theory Cartesian {
      include .rel_orders.Order
      include .rel_orders.Infimum
      include .rel_orders.TopElement
  }

  theory CoCartesian {
      include .rel_orders.Order
      include .rel_orders.Supremum
      include .rel_orders.BottomElement
  }

  theory BoundedLatticeOrder {
      include LatticeOrder
      include Cartesian
      include CoCartesian
  }
}
