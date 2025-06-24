module Components {
  type nat = int[0;]

  theory Vector {
    x: float
    y: float
    z: float
    length: float
  }


  theory Point {
    x: float
    y: float
    z: float

    translate = (v: Vector) -> Point {x=..x+v.x, y=..y+v.y, z=..z+v.z}
  }

  theory Triangle {
    a: Point
    b: Point
    c: Point
  }

  theory Cylinder {
    base: Point
    radius: float
    orientation: Vector

    translate = (v: Vector) -> Cylinder {
      base = ..base.translate(v)
      radius = ..radius
      orientation = ..orientation
    }
  }

  theory CogWheel {
    center: Point
    radius: float
    teeth: nat

    translate = (v: Vector) -> CogWheel {
      center = ..center.translate(v)
      radius = ..radius
      teeth = ..teeth
    }
  }

}
