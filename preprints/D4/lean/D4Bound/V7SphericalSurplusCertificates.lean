import D4Bound.V7SphericalSurplus
import D4Bound.SphericalSurplusSignTriangle0
import D4Bound.SphericalSurplusSignTriangle1
import D4Bound.SphericalSurplusSignTriangle2

/-! Exact interface between the three finite Bernstein replays and the actual
V7 census energy. Each cube premise is supplied by its complete replay; this
module does not replace a replay with a certificate acceptance flag. -/
namespace D4Bound.V7
open SphericalSurplusSign SphericalSurplusSign.Bernstein16

theorem triangleSign0_of_cube (h : OnCube upper0 gramUpper0) :
    SphericalSurplusBounds.B0.TriangleSign := rawTriangle0_of_cube h

theorem triangleSign1_of_cube (h : OnCube upper1 gramUpper1) :
    SphericalSurplusBounds.B1.TriangleSign := rawTriangle1_of_cube h

theorem triangleSign2_of_cube (h : OnCube upper2 gramUpper2) :
    SphericalSurplusBounds.B2.TriangleSign := rawTriangle2_of_cube h

theorem surplus_floor_of_cubes
    (h0 : OnCube upper0 gramUpper0)
    (h1 : OnCube upper1 gramUpper1)
    (h2 : OnCube upper2 gramUpper2)
    (X : Finset E4) (hX : Admissible X) (hC : InCountDomain X) :
    CensusArithmetic.surplusPart (CensusArithmetic.ofNeighbourhood X) ≤ sphericalEnergy X :=
  surplus_floor_of_triangles
    (triangleSign0_of_cube h0) (triangleSign1_of_cube h1) (triangleSign2_of_cube h2) X hX hC

#print axioms triangleSign0_of_cube
#print axioms triangleSign1_of_cube
#print axioms triangleSign2_of_cube
#print axioms surplus_floor_of_cubes
end D4Bound.V7
