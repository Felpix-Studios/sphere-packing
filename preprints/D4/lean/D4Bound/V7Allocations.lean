import D4Bound.V7CountEnergy
import D4Bound.V7Radial
import D4Bound.ComponentsCapacity

/-! The two actual antipodal allocation components have nonnegative energy.
This connects their piecewise squared-distance definitions to the proved
classical and two-level capacities. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

theorem allocationProfile_pstar (c : AllocationData) (hc : c.twoLevel = false)
    {r : ℝ} (hr : 0 ≤ r) : allocationProfile c (r^2) = Components.capPstar r := by
  simp only [allocationProfile, hc, Bool.false_eq_true, if_false, Real.sqrt_sq hr]
  by_cases hbig : 1/2 ≤ r^2
  · have hrhalf : 1/2 ≤ r := by nlinarith
    rw [if_pos hbig, Components.capPstar_eq_capP hrhalf,
      Components.capP, max_eq_left (by linarith)]
  · rw [if_neg hbig]
    by_cases hmid : 1/4 ≤ r^2
    · have hrhalf : 1/2 ≤ r := by nlinarith
      rw [if_pos hmid, Components.capPstar_eq_capP hrhalf,
        Components.capP, max_eq_right (by linarith)]
    · rw [if_neg hmid, Components.capPstar, if_pos (by nlinarith)]

theorem allocationProfile_step (c : AllocationData) (hc : c.twoLevel = true)
    (ha : (0 : ℝ) ≤ c.inner) (hb : (0 : ℝ) ≤ c.outer) {r : ℝ} (hr : 0 ≤ r) :
    allocationProfile c (r^2) = Components.capStep c.inner c.outer r := by
  simp only [allocationProfile, hc, if_true, Components.capStep,
    sq_lt_sq₀ hr ha, sq_le_sq₀ hr hb]

theorem radial_sum_square {x y : E4} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖*‖x‖ + ‖y‖*‖y‖ + 2*‖x‖*‖y‖*(⟪x,y⟫/(‖x‖*‖y‖)) = ‖x+y‖^2 := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [norm_add_sq_real]
  field_simp
  <;> ring

def allocationValue (c : AllocationData) (X : Finset E4) : ℝ :=
  ∑ y ∈ X, (c.weight : ℝ)*radialValue c.vector ‖y‖ *
    (1 - ∑ x ∈ X, allocationProfile c (‖x+y‖^2))

theorem allocation_component_identity (c : AllocationData) (X : Finset E4)
    (hX : (0 : E4) ∉ X) :
    radialEnergy 0 (fun r => (c.weight : ℝ)*radialValue c.vector r/2)
      (fun r s t => -(c.weight : ℝ)*(radialValue c.vector r+radialValue c.vector s)*
        allocationProfile c (r*r+s*s+2*r*s*t)/2) X = allocationValue c X := by
  let u := fun x : E4 => (c.weight : ℝ)*radialValue c.vector ‖x‖
  let cap := fun y x : E4 => allocationProfile c (‖x+y‖^2)
  have hn : ∀ x ∈ X, x ≠ 0 := fun x hx he => hX (he ▸ hx)
  have h0 : Components.usageKernel u cap 0 0 = 0 := by simp [Components.usageKernel]
  have h1 : (∑ x ∈ X, Components.usageKernel u cap x 0) =
      ∑ x ∈ X, (c.weight : ℝ)*radialValue c.vector ‖x‖/2 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp [Components.usageKernel, hn x hx, u]
  have h2 : (∑ x ∈ X, ∑ y ∈ X, Components.usageKernel u cap x y) =
      ∑ x ∈ X, ∑ y ∈ X, -(c.weight : ℝ)*
        (radialValue c.vector ‖x‖+radialValue c.vector ‖y‖)*
        allocationProfile c (‖x‖*‖x‖+‖y‖*‖y‖+2*‖x‖*‖y‖*(⟪x,y⟫/(‖x‖*‖y‖)))/2 := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    rw [radial_sum_square (hn x hx) (hn y hy)]
    simp only [Components.usageKernel, if_neg (hn x hx), if_neg (hn y hy), u, cap]
    rw [add_comm y x]
    ring
  have h := Components.usage_energy_eq u cap X hX
  rw [Components.anchoredEnergy, h0, h1, h2] at h
  exact h

theorem allocations_energy_identity (X : Finset E4) (hX : (0 : E4) ∉ X) :
    allocationsEnergy X = (allocations.map fun c => allocationValue c X).sum := by
  unfold allocationsEnergy allocationsLinear allocationsCorrection
  have hz : (allocations.map fun _ => (0 : ℝ)).sum = 0 := by simp
  rw [← hz]
  have hneg : ∀ r s t : ℝ,
      -(allocations.map fun c => (c.weight : ℝ)*
        (radialValue c.vector r+radialValue c.vector s)*allocationProfile c (r*r+s*s+2*r*s*t)/2).sum =
      (allocations.map fun c => -(c.weight : ℝ)*
        (radialValue c.vector r+radialValue c.vector s)*allocationProfile c (r*r+s*s+2*r*s*t)/2).sum := by
    intro r s t
    rw [List.sum_neg]
    simp only [List.map_map, Function.comp_def, neg_div, neg_mul]
  simp_rw [hneg]
  rw [radialEnergy_list]
  simp_rw [allocation_component_identity _ _ hX]

theorem allocation_data_ok : ∀ c ∈ allocations,
    (0 : ℚ) ≤ c.weight ∧ (∀ q ∈ c.vector, 0 ≤ q) ∧
    (c.twoLevel = true → 0 ≤ c.inner ∧ c.inner ≤ c.outer ∧
      c.inner+c.outer ≤ 1 ∧ 3*c.outer^2 < 1) := by
  decide +kernel

theorem allocations_energy_nonneg {X : Finset E4} (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) : 0 ≤ allocationsEnergy X := by
  have hn : (0 : E4) ∉ X := by
    intro h
    have h1 := hX.1 0 h
    norm_num at h1
  rw [allocations_energy_identity X hn]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hw, hv, hs⟩ := allocation_data_ok c hc
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · exact mul_nonneg (Rat.cast_nonneg.mpr hw) (radialValue_nonneg _ hv (hX.1 y hy) (hR y hy))
  · apply sub_nonneg.mpr
    have hsep : Components.UnitSep X := hX.2
    cases ht : c.twoLevel with
    | false =>
      simp_rw [allocationProfile_pstar c ht (norm_nonneg _)]
      simpa only [sub_neg_eq_add] using Components.pstar_capacity X hsep (-y)
    | true =>
      obtain ⟨h0, hab, hsum, hb⟩ := hs ht
      have h0R : (0 : ℝ) ≤ c.inner := Rat.cast_nonneg.mpr h0
      have habR : (c.inner : ℝ) ≤ c.outer := Rat.cast_le.mpr hab
      have hsumR : (c.inner : ℝ)+(c.outer : ℝ) ≤ 1 := by exact_mod_cast hsum
      have hbR : (3 : ℝ)*(c.outer : ℝ)^2 < 1 := by exact_mod_cast hb
      simp_rw [allocationProfile_step c ht h0R (h0R.trans habR) (norm_nonneg _)]
      simpa only [sub_neg_eq_add] using Components.step_capacity
        c.inner c.outer habR hsumR hbR X hsep (-y)

end
end D4Bound.V7
