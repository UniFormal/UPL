module slingshot_example{
  type point
  dist: point -> point -> float
  
  theory Slingshot_schema{
    launch: point
    launch_base: point
    h_launch: float
    h_launch_P: |- h_launch == dist(launch_base)(launch)
    v_z: float // vertical launch velocity (along the z-axis)
    v_x: float // horizontal launch velocity (x- and y-axis are indiscernible)
    v_launch: float
    v_launch_Ax: |- v_launch == Math.sqrt(v_z*v_z + v_x*v_x)
    inclination_launch: float
    inclination_Ax: |- inclination_launch == (v_z / v_x)

    target: point
    dist_target: float
    dist_target_P: |- dist_target == dist(launch_base)(target)

    grav_acc: float = -9.81 // negative, because that fits the usual formulas 
    // Just the quadratic formula, with the implicit knowledge that this is the positive solution (grac_acc < 0)
    impact_time: float = (- v_z - Math.sqrt((v_z*v_z) - 4*h_launch*grav_acc))/2*grav_acc
    // There is no horizontal acceleration or offset (Yes, we ignore air-resistance)
    // impact_distance: float = v_x * impact_time
    // impact_distance_Ax: |- impact_distance == dist_target

    // We don't actually care about the impact_distance, only that it is on target => just substitute it immediately
    impact_at_target_Ax: |- v_x * impact_time == dist_target
  }

  // fixing the launch angle to a convenient value 
  theory Slingshot_fixed_angle{
    launch: point
    launch_base: point
    h_launch: float
    h_launch_P: |- h_launch == dist(launch_base)(launch)
    v_z: float // vertical launch velocity (along the z-axis)
    v_x: float // horizontal launch velocity (x- and y-axis are indiscernible)
    v_launch: float
    inclination_launch = 8/15
    // about that inclination:
    // $sqrt(x^2+(ax)^2) = sqrt((a^2+1) * x^2) = sqrt(a^2+1)*x$ (for x>0)
    // we want $a$ s.t. $sqrt(a^2+1) = n/m$ rational, and  $(n/m)^2 +1 = (n^2/m^2) + (m^2/m^2) = (n^2+m^2)/m^2$ 
    // so, we want $n^2+m^2 = k^2$, i.e. a [Pythagorean triple](https://en.wikipedia.org/wiki/Pythagorean_triple)
    // looking through them, we find (8,15,17), which is nice, because 15/8 and 17/8 both have exact float representations.
    // We chose v_z as basis, because it occurs more often. 
    // (The inclination is defined v_z/v_x though, so *shrug*)
    inclination_Ax: |- inclination_launch == (v_z / v_x)
    // sqrt(x^2+(15/8x)^2) == sqrt((15^2+8^2)/(8^2) * x^2) == 17/8x = 2.125x, see above
    v_launch_Ax: |- v_launch == 2.125 * v_z 

    target: point
    dist_target: float
    dist_target_P: |- dist_target == dist(launch_base)(target)

    grav_acc: float = 9.81 
    // Just the quadratic formula for b = v_z, c = h_launch and a = -1/2*grav_acc
    // the (-1/2) part is canceled implicitly
    impact_time: float = (v_z + Math.sqrt((v_z*v_z) + 2*h_launch*grav_acc))/grav_acc
    // There is no horizontal acceleration or offset (Yes, we ignore air-resistance)
    // impact_distance: float = v_x * impact_time
    // impact_distance_Ax: |- impact_distance == dist_target

    // We don't actually care about the impact_distance, only that it is on target => just substitute it immediately
    impact_at_target_Ax: |- v_x * impact_time == dist_target
  }

  theory Slingshot_simple{
    h_launch: float
    v_z: float // vertical launch velocity (along the z-axis)
    v_x: float // horizontal launch velocity (x- and y-axis are indiscernible)
    v_launch: float
    inclination_launch = 8/15
    // about that inclination:
    // $sqrt(x^2+(ax)^2) = sqrt((a^2+1) * x^2) = sqrt(a^2+1)*x$ (for x>0)
    // we want $a$ s.t. $sqrt(a^2+1) = n/m$ rational, and  $(n/m)^2 +1 = (n^2/m^2) + (m^2/m^2) = (n^2+m^2)/m^2$ 
    // so, we want $n^2+m^2 = k^2$, i.e. a [Pythagorean triple](https://en.wikipedia.org/wiki/Pythagorean_triple)
    // looking through them, we find (8,15,17), which is nice, because 15/8 and 17/8 both have exact float representations.
    // We chose v_z as basis, because it occurs more often. 
    // (The inclination is defined v_z/v_x though, so *shrug*)
    inclination_Ax: |- inclination_launch == (v_z / v_x)
    // sqrt(x^2+(15/8x)^2) == sqrt((15^2+8^2)/(8^2) * x^2) == 17/8x = 2.125x, see above
    v_launch_Ax: |- v_launch == 2.125 * v_z 

    dist_target: float

    grav_acc: float = 9.81 
    // Just the quadratic formula for b = v_z, c = h_launch and a = -1/2*grav_acc
    // the (-1/2) part is canceled implicitly
    impact_time: float = (v_z + Math.sqrt((v_z*v_z) + 2*h_launch*grav_acc))/grav_acc
    // There is no horizontal acceleration or offset (Yes, we ignore air-resistance)
    // impact_distance: float = v_x * impact_time
    // impact_distance_Ax: |- impact_distance == dist_target

    // We don't actually care about the impact_distance, only that it is on target => just substitute it immediately
    impact_at_target_Ax: |- v_x * impact_time == dist_target
  }

  theory Slingshot_test{
    h_launch = 1.0
    dist_target = 7.5
    include Slingshot_fixed_angle
  }
}