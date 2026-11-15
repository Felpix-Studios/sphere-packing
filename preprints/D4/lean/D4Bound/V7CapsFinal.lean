import D4Bound.SphereMeasureCap
import D4Bound.SphereMeasureTransport

/-! Nonnegativity of all 98 cap terms of the concrete V7 kernel.
The common transverse measure and every closed-cap marginal are proved. -/
namespace D4Bound.V7

theorem caps_energy_nonneg {X : Finset E4} (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) : 0 ≤ capsEnergy X :=
  caps_energy_nonneg_of_transverse_laws
    (SphereMeasure.transverse_laws_of_cap_formula SphereMeasure.uniformSphere_cap) hX hR

end D4Bound.V7

#print axioms D4Bound.V7.caps_energy_nonneg
