import D4Bound.V7Caps
import D4Bound.V7Allocations
import D4Bound.V7Gram

/-! A polynomial upper bound for the complete ungauged pair expression.
Only nonnegative self corrections are discarded; cap truncations are restored.
This avoids any cap-probability branch in the one-variable sign certificate. -/
open Finset
namespace D4Bound.V7
noncomputable section
open Classical

def uncutLinear (r : ℝ) : ℝ :=
  radialValue originVector r +
  (caps.map fun c => (c.weight : ℝ)*(c.multiplicity : ℝ)*radialValue c.vector r/2).sum +
  (tents.map fun c => (c.weight : ℝ)*(c.capacity : ℝ)*radialValue c.vector r/2).sum +
  (allocations.map fun c => (c.weight : ℝ)*radialValue c.vector r/2).sum +
  (sphericalRays.map fun c => (c.weight : ℝ)*(c.bound : ℝ)*indicator c.radius r/2).sum +
  (conditionalRays.map fun c => 23*(c.weight : ℝ)*
    (indicator c.outer r-indicator c.inner r)/2).sum +
  (countPolynomials.map fun c => countLinear c r).sum

def diagonalUpper (r : ℝ) : ℝ :=
  2*uncutLinear r + gramPair r r 1 + sphericalPair r r 1 + conditionalPair r r +
    (countPolynomials.map fun c => countPair c r r).sum

lemma list_sum_map_mono {α : Type*} (L : List α) (f g : α → ℝ)
    (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma capWeight_le_radial {c : Cap} (hc : CapValid c) {r : ℝ}
    (h1 : 1 ≤ r) (hR : r ≤ 7/4) : capWeight c r ≤ radialValue c.vector r := by
  have hv := radialValue_nonneg c.vector hc.2.2.2.2.2.1 h1 hR
  unfold capWeight
  cases c.cutoff <;> simp only
  · exact le_rfl
  · split_ifs <;> first | exact le_rfl | exact hv

lemma caps_multiplicity_nonneg : ∀ c ∈ caps, (0 : ℚ) ≤ c.multiplicity := by
  decide +kernel

lemma rawLinear_le_uncut {r : ℝ} (h1 : 1 ≤ r) (hR : r ≤ 7/4) :
    rawLinear r ≤ uncutLinear r := by
  have hc := list_sum_map_mono caps
    (fun c => (c.weight : ℝ)*(c.multiplicity : ℝ)*capWeight c r/2)
    (fun c => (c.weight : ℝ)*(c.multiplicity : ℝ)*radialValue c.vector r/2) (by
      intro c hc
      have hv := caps_data_valid c hc
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (capWeight_le_radial hv h1 hR)
        (mul_nonneg (Rat.cast_nonneg.mpr hv.2.2.2.2.1)
          (Rat.cast_nonneg.mpr (caps_multiplicity_nonneg c hc))))
  unfold rawLinear uncutLinear
  linarith

lemma capProbability_nonneg (c : Cap) (r t : ℝ) : 0 ≤ capProbability c r t := by
  unfold capProbability
  dsimp only
  split_ifs <;> first | norm_num | exact le_max_left _ _

lemma capsCorrection_nonneg {r s : ℝ} (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hrR : r ≤ 7/4) (hsR : s ≤ 7/4) (t : ℝ) : 0 ≤ capsCorrection r s t := by
  unfold capsCorrection
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  have hv := caps_data_valid c hc
  exact div_nonneg (mul_nonneg (Rat.cast_nonneg.mpr hv.2.2.2.2.1)
    (add_nonneg (mul_nonneg (capWeight_nonneg hv hs1 hsR) (capProbability_nonneg c r t))
      (mul_nonneg (capWeight_nonneg hv hr1 hrR) (capProbability_nonneg c s t)))) (by norm_num)

lemma tentsCorrection_nonneg {r s : ℝ} (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hrR : r ≤ 7/4) (hsR : s ≤ 7/4) (t : ℝ) : 0 ≤ tentsCorrection r s t := by
  unfold tentsCorrection
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hw,hv,_⟩ := tent_data_ok c hc
  exact div_nonneg (mul_nonneg (Rat.cast_nonneg.mpr hw)
    (add_nonneg (mul_nonneg (radialValue_nonneg _ hv hs1 hsR) (le_max_left _ _))
      (mul_nonneg (radialValue_nonneg _ hv hr1 hrR) (le_max_left _ _)))) (by norm_num)

lemma allocationProfile_nonneg (c : AllocationData) (q : ℝ) : 0 ≤ allocationProfile c q := by
  unfold allocationProfile
  split_ifs <;> (try norm_num) <;> (try positivity) <;> linarith

lemma allocationsCorrection_nonneg {r s : ℝ} (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hrR : r ≤ 7/4) (hsR : s ≤ 7/4) (t : ℝ) : 0 ≤ allocationsCorrection r s t := by
  unfold allocationsCorrection
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hw,hv,_⟩ := allocation_data_ok c hc
  exact div_nonneg (mul_nonneg (mul_nonneg (Rat.cast_nonneg.mpr hw)
    (add_nonneg (radialValue_nonneg _ hv hr1 hrR) (radialValue_nonneg _ hv hs1 hsR)))
    (allocationProfile_nonneg c _)) (by norm_num)

lemma graph_weights_nonneg : ∀ g ∈ graphs, (0 : ℚ) ≤ g.weight := by decide +kernel

lemma graphsCorrection_nonneg (r s t : ℝ) : 0 ≤ graphsCorrection r s t := by
  unfold graphsCorrection
  apply List.sum_nonneg
  intro a ha
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
  split_ifs
  · exact Rat.cast_nonneg.mpr (graph_weights_nonneg g hg)
  · norm_num

/-- Sufficient polynomial comparison for the actual one-variable gauge weight. -/
theorem ungaugedPair_le_upper {r : ℝ} (h1 : 1 ≤ r) (hR : r ≤ 7/4) :
    ungaugedPair r ≤ scalarRadius r + diagonalUpper r := by
  have h := rawLinear_le_uncut h1 hR
  have hc := capsCorrection_nonneg h1 h1 hR hR (1 : ℝ)
  have ht := tentsCorrection_nonneg h1 h1 hR hR (1 : ℝ)
  have ha := allocationsCorrection_nonneg h1 h1 hR hR (1 : ℝ)
  have hg := graphsCorrection_nonneg r r 1
  unfold ungaugedPair rawPair diagonalUpper
  linarith

/-- A Taylor lower bound suffices because the polynomial part is nonpositive. -/
theorem pair_sign_of_taylor (r D : ℝ) (n : ℕ) (hD : D ≤ 0)
    (hp : F (2*r^2) + D*(∑ i ∈ range n, (2*r^2)^i / i.factorial) ≤ 0) :
    scalarRadius r + D ≤ 0 := by
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ 2*r^2 by positivity) n
  have hm := mul_le_mul_of_nonpos_left he hD
  have hpos := Real.exp_pos (2*r^2)
  have hcancel : Real.exp (2*r^2) * scalarRadius r = F (2*r^2) := by
    rw [scalarRadius,← mul_assoc,← Real.exp_add]
    simp
  have htotal : Real.exp (2*r^2)*(scalarRadius r+D) ≤ 0 := by
    rw [mul_add,hcancel]
    nlinarith
  by_contra h
  have hh := mul_pos hpos (lt_of_not_ge h)
  linarith

end
end D4Bound.V7
