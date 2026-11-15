import D4Bound.V7CensusFromSigns
import D4Bound.V7SphericalSurplusCertificates

/-! The concrete census floor from exactly the three degree-16 cube
certificates. Each hypothesis is the conclusion of one complete replay,
`SphericalSurplusSign.Bernstein16.GeneratedN.onCube` for N = 0, 1, 2. -/
namespace D4Bound.V7
open SphericalSurplusSign SphericalSurplusSign.Bernstein16

theorem censusFloor_of_cubes
    (h0 : OnCube upper0 gramUpper0)
    (h1 : OnCube upper1 gramUpper1)
    (h2 : OnCube upper2 gramUpper2) : CensusFloor kernel :=
  censusFloor_of_triangles
    (triangleSign0_of_cube h0) (triangleSign1_of_cube h1) (triangleSign2_of_cube h2)

end D4Bound.V7

#print axioms D4Bound.V7.censusFloor_of_cubes
