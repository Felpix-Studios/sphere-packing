import D4Bound.V7Census
import D4Bound.V7SphericalSurplus

/-! The concrete census floor needs only the three physical spherical triangle
signs. Every other component and all finite count cases are proved. The signs
remain explicit until the complete degree-16 certificate replay supplies them. -/
namespace D4Bound.V7

theorem censusFloor_of_triangles
    (h0 : SphericalSurplusBounds.B0.TriangleSign)
    (h1 : SphericalSurplusBounds.B1.TriangleSign)
    (h2 : SphericalSurplusBounds.B2.TriangleSign) : CensusFloor kernel := by
  apply censusFloor_of_component_bounds
  intro X hX _ hD
  exact surplus_floor_of_triangles h0 h1 h2 X hX hD

end D4Bound.V7

#print axioms D4Bound.V7.censusFloor_of_triangles
