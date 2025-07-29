module Components {
  type nat = int[0;]
  type point
  type line
  on: (point, line) -> bool
  type vector
  translate: point -> vector -> point

  theory Triangle {
    a: point
    b: point
    c: point
  }

  theory Vector3D {
    x: float
    y: float
    z: float
    length: float = ???
  }

  theory Point3D {
    x: float
    y: float
    z: float
  }

  theory Space3D{
    type point = Point3D
    type vector = Vector3D
    type line = (point, vector)

    translate = (p: point) -> (v:vector) ->  Point3D{x=p.x+v.x, y=p.y+v.y, z=p.z+v.z}
  }

  theory Cylinder {
    base: point
    radius: float
    orientation: vector

    translat = (v: vector) -> Cylinder {
      base = translate(base)(v)
      radius = ..radius
      orientation = ..orientation
    }
  }

  theory CogWheel {
    center: point
    radius: float
    teeth: nat

    val translate = (v: vector) -> CogWheel {
      center = translate(center)(v)
      radius = ..radius
      teeth = ..teeth
    }
  }

}
