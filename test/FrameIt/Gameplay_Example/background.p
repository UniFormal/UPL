// The Background declares all relevant types and functions
// No modules, because UPL struggles with modules rn
type point
type triangle = (point,point,point)
dist: point -> point -> float
similar: triangle -> triangle -> bool
