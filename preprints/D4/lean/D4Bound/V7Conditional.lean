import D4Bound.V7CountEnergy

/-! The two conditional count rays of the actual V7 kernel. Their energies
are the exact count products already present in `InCountDomain`. -/
open Finset
namespace D4Bound.V7
noncomputable section
open Classical

def conditionalValue (c : ConditionalRay) (X : Finset E4) : ℝ :=
  (c.weight : ℝ) * (23 - (countWithin X (c.inner : ℝ) : ℝ)) *
    ((countWithin X (c.outer : ℝ) : ℝ) - (countWithin X (c.inner : ℝ) : ℝ))

theorem conditional_component_identity (c : ConditionalRay) (X : Finset E4) :
    radialEnergy 0
      (fun r => 23*(c.weight : ℝ)*(indicator c.outer r-indicator c.inner r)/2)
      (fun r s _ => -(c.weight : ℝ) *
        (indicator c.inner r*(indicator c.outer s-indicator c.inner s) +
          (indicator c.outer r-indicator c.inner r)*indicator c.inner s)/2) X =
      conditionalValue c X := by
  unfold radialEnergy conditionalValue
  simp only [mul_add, mul_sub, add_div, sub_div, neg_div,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, indicator_sum]
  ring

theorem conditional_energy_identity (X : Finset E4) :
    conditionalEnergy X = (conditionalRays.map fun c => conditionalValue c X).sum := by
  unfold conditionalEnergy conditionalLinear conditionalPair
  have hz : (conditionalRays.map fun _ => (0 : ℝ)).sum = 0 := by simp
  rw [← hz, radialEnergy_list]
  simp_rw [conditional_component_identity]

theorem conditional_energy_nonneg {X : Finset E4} (hD : InCountDomain X) :
    0 ≤ conditionalEnergy X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ha, hb⟩ := hD
  have ha' : (0 : ℝ) ≤ (23 - (countWithin X R1 : ℝ)) *
      ((countWithin X R5 : ℝ) - (countWithin X R1 : ℝ)) := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ (23 - (countWithin X R2 : ℝ)) *
      ((countWithin X R4 : ℝ) - (countWithin X R2 : ℝ)) := by exact_mod_cast hb
  rw [conditional_energy_identity]
  simp only [conditionalRays, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, conditionalValue]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  change 0 ≤ (4623853358732678829 / 125000000000000000000000 : ℝ) *
    (23 - (countWithin X R2 : ℝ)) *
      ((countWithin X R4 : ℝ) - (countWithin X R2 : ℝ)) +
    (65804842507510742427 / 2000000000000000000000000 : ℝ) *
    (23 - (countWithin X R1 : ℝ)) *
      ((countWithin X R5 : ℝ) - (countWithin X R1 : ℝ))
  exact add_nonneg
    (by rw [mul_assoc]; exact mul_nonneg (by norm_num) hb')
    (by rw [mul_assoc]; exact mul_nonneg (by norm_num) ha')

end
end D4Bound.V7
