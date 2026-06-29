module Slingshot{
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
    v_launch_Ax: |- v_launch == (v_z^2 + v_x^2)^(1/2)
    inclination_launch: float
    inclination_Ax: |- inclination_launch == (v_z / v_x)

    target: point
    dist_target: float 
    dist_target_P: |- dist_target == dist(launch_base)(target)

    grav_acc: float = 9.81 
    // Just the quadratic formula for b = v_z, c = h_launch and a = -1/2*grav_acc
    // both (-1/2) are canceled implicitly
    impact_time: float = (v_z + Math.sqrt((v_z*v_z) + 2*h_launch*grav_acc))/grav_acc
    // There is no horizontal acceleration or offset (Yes, we ignore air-resistance)
    // impact_distance: float = v_x * impact_time
    // impact_distance_Ax: |- impact_distance == dist_target 

    // We don't actually care about the impact_distance, only that it is on target => just substitute it immediately
    impact_at_target_Ax: |- v_x * impact_time == dist_target
  }

  // launch with no height offset
  theory Slingshot_groundLaunch{
    launch: point
    launch_base: point = launch
    h_launch: float = 0
    h_launch_P: |- dist(launch_base)(launch) == h_launch
    v_z: float // vertical launch velocity (along the z-axis)
    v_x: float // horizontal launch velocity (x- and y-axis are indiscernible)
    v_launch: float
    v_launch_Ax: |- (v_z^2 + v_x^2) == v_launch^2
    inclination_launch: float
    inclination_Ax: |- inclination_launch == (v_z / v_x)

    target: point
    dist_target: float
    dist_target_P: |- dist(launch_base)(target) == dist_target

    grav_acc: float = 9.81 
    // Just the quadratic formula for b = v_z, c = h_launch and a = -1/2*grav_acc
    // both (-1/2) are canceled implicitly
    impact_time: float
    impact_time_Ax: |- (v_z + ((v_z*v_z) + 2*h_launch*grav_acc)^(1/2))/grav_acc == impact_time

    // There is no horizontal acceleration or offset (Yes, we ignore air-resistance)
    // impact_distance: float = v_x * impact_time
    // impact_distance_Ax: |- impact_distance == dist_target

    // We don't actually care about the impact_distance, only that it is on target => just substitute it immediately
    impact_at_target_Ax: |- v_x * impact_time == dist_target
    
    // //
    // Simplifications from our assumptions:
    // //

    // The quadratic formula for b = v_z, c = 0 and a = -1/2*grav_acc, with implicit cancelling:
    // sqrt(v_z^2 - 4*0*..) ~> v_z
    // -v_z +- v_z ~> -v_z - v_z (We don't care about the root at 0)
    // 2*(-1/2*grav_acc) ~> -grav_acc
    // (-v_z - v_z) / (-grav_acc) ~> 2*v_z / grav_acc
    impact_time_Ax_Fixed: |- 2*v_z / grav_acc == impact_time

    // equate `impact_at_target_Ax` and `impact_time_Ax_Fixed` (the two calculations of `impact_time`), 
    // rearrange and use `inclination_Ax`
    // equated: |- dist_target * grav_acc == 2*v_z*v_x
    impact_at_time_Fixed: |- dist_target * grav_acc  == 2 * inclination_launch * (v_x^2)
    impact_at_time_Fixed2: |- v_x^2 == dist_target * grav_acc / 2 / inclination_launch
  }

  // fixing the launch angle to a convenient value 
  theory Slingshot_fixedAngle{
    launch: point
    launch_base: point
    h_launch: float
    h_launch_P: |- h_launch == dist(launch_base)(launch)
    v_z: float // vertical launch velocity (along the z-axis)
    v_x: float // horizontal launch velocity (x- and y-axis are indiscernible)
    v_launch: float
    inclination_launch = 0.75 // == 3/4
    // about that inclination:
    // $sqrt(x^2+(ax)^2) = sqrt((a^2+1) * x^2) = sqrt(a^2+1)*x$ (for x>0)
    // we want $a$ s.t. $sqrt(a^2+1) = n/m$ rational, and  $(n/m)^2 +1 = (n^2/m^2) + (m^2/m^2) = (n^2+m^2)/m^2$ 
    // so, we want $n^2+m^2 = k^2$, i.e. a [Pythagorean triple](https://en.wikipedia.org/wiki/Pythagorean_triple)
    // We pick the simplest one (3,4,5), because 3/4 and 5/4 both have exact float representations.
    // We chose v_z as basis, because it occurs more often. 
    // (The inclination is defined v_z/v_x though, so *shrug*)
    inclination_Ax: |- inclination_launch == (v_z / v_x)
    // sqrt(x^2+(3/4x)^2) == sqrt((4^2+3^2)/(4^2) * x^2) == 5/4x = 1.25x, see above
    v_launch_Ax_Fixed: |- 1.25 * v_x == v_launch

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

  // both 
  theory Slingshot_fixedAngle_groundLaunch{
    launch: point
    launch_base: point = launch
    h_launch: float = 0
    h_launch_P: |- dist(launch_base)(launch) == h_launch
    v_z: float // vertical launch velocity (along the z-axis)
    v_x: float // horizontal launch velocity (x- and y-axis are indiscernible)
    v_launch: float
    inclination_launch = 0.75 // == 3/4
    // about that inclination:
    // $sqrt(x^2+(ax)^2) = sqrt((a^2+1) * x^2) = sqrt(a^2+1)*x$ (for x>0)
    // we want $a$ s.t. $sqrt(a^2+1) = n/m$ rational, and  $(n/m)^2 +1 = (n^2/m^2) + (m^2/m^2) = (n^2+m^2)/m^2$ 
    // so, we want $n^2+m^2 = k^2$, i.e. a [Pythagorean triple](https://en.wikipedia.org/wiki/Pythagorean_triple)
    // We pick the simplest one (3,4,5), because 3/4 and 5/4 both have exact float representations.
    // We chose v_z as basis, because it occurs more often. 
    // (The inclination is defined v_z/v_x though, so *shrug*)
    inclination_Ax: |- inclination_launch == (v_z / v_x)

    v_launch_Ax: |- Math.sqrt(v_z*v_z + v_x*v_x) == v_launch

    target: point
    dist_target: float
    dist_target_P: |- dist(launch_base)(target) == dist_target

    grav_acc: float = 10 

    impact_time: float
    // impact_time_P: |- (v_z + Math.sqrt((v_z*v_z) + 2*h_launch*grav_acc))/grav_acc ==  impact_time

    // There is no horizontal acceleration or offset (Yes, we ignore air-resistance)
    // impact_distance: float = v_x * impact_time
    // impact_distance_Ax: |- impact_distance == dist_target

    // We don't actually care about the impact_distance, only that it is on target => just substitute it immediately
    impact_at_target_Ax: |- v_x * impact_time == dist_target
    
    // //
    // Simplifications from our assumptions:
    // //
    inclination_Ax_Fixed: |- v_x * 0.75 == v_z
    inclination_Ax_Fixed2: |- v_z / 0.75 == v_x

    // sqrt(x^2+(3/4x)^2) == sqrt((4^2+3^2)/(4^2) * x^2) == 5/4x = 1.25x, see above
    v_launch_Ax_Fixed: |- 1.25 * v_x == v_launch

    // The quadratic formula for b = v_z, c = 0 and a = -1/2*grav_acc, with implicit cancelling:
    // sqrt(v_z^2 - 4*0*..) ~> v_z
    // -v_z +- v_z ~> -v_z - v_z (We don't care about the root at 0)
    // 2*(-1/2*grav_acc) ~> -grav_acc
    // (-v_z - v_z) / (-grav_acc) ~> 2*v_z / grav_acc
    impact_time_P_Fixed: |- 2*v_z / grav_acc == impact_time

    // equate the two calculations of `impact_time`, and rearrange
    impact_at_time_Fixed: |- dist_target * grav_acc == 2*v_z*v_x
    impact_at_time_Fixed2: |- dist_target * grav_acc == 2*0.75* v_x^2

    // plugging `inclination_Ax_Fixed2` into `impact_at_target_Ax`
    impact_at_target_Ax_Fixed2: |- (v_z / 0.75) * impact_time == dist_target
    // reorder and equate with `impact_time_P_Fixed`
    equated1: |- 2*v_z / grav_acc == dist_target * 0.75 / v_z 
    equated2: |- 2*v_z*v_z == dist_target * 0.75 * grav_acc
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
    // h_launch = 1.0
    dist_target = 3.75 // == 15/4, because WolframAlpha said that this has a neat solution
    inclination_launch = 0.75
    include Slingshot_groundLaunch
  }
}