import D4Bound.V7CountEnergy
import D4Bound.V7Radial
import D4Bound.ComponentsTent

/-! Exact positivity of all four concrete pointed-tent components. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

theorem weighted_usage_identity (X : Finset E4) (C : ℝ)
    (u : E4 → ℝ) (cap : E4 → E4 → ℝ) :
    2*(∑ x ∈ X, C*u x/2) +
      (∑ x ∈ X, ∑ y ∈ X, -(u y*cap y x+u x*cap x y)/2) =
    ∑ y ∈ X, u y*(C-∑ x ∈ X, cap y x) := by
  have hs : (∑ x ∈ X, ∑ y ∈ X, u y*cap y x) =
      ∑ x ∈ X, ∑ y ∈ X, u x*cap x y := Finset.sum_comm
  have hp : (∑ x ∈ X, ∑ y ∈ X, -(u y*cap y x+u x*cap x y)/2) =
      -(∑ x ∈ X, ∑ y ∈ X, u x*cap x y) := by
    simp only [neg_div, Finset.sum_neg_distrib, add_div,
      Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hs]
    ring
  rw [hp, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

theorem tentProfile_coordinates (d : ℝ) {x y : E4} (hx : x ≠ 0) (hy : y ≠ 0) :
    tentProfile d ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) = Components.capP ‖x+d • dir y‖ := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  unfold tentProfile Components.capP
  congr 2
  rw [norm_add_sq_real, norm_smul, norm_dir hy, mul_one, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, dir, real_inner_smul_right]
  field_simp
  <;> ring

def tentValue (c : Tent) (X : Finset E4) : ℝ :=
  ∑ y ∈ X, (c.weight : ℝ)*radialValue c.vector ‖y‖ *
    ((c.capacity : ℝ) - ∑ x ∈ X, Components.capP ‖x+(c.d : ℝ) • dir y‖)

theorem tent_component_identity (c : Tent) (X : Finset E4) (hX : (0 : E4) ∉ X) :
    radialEnergy 0 (fun r => (c.weight : ℝ)*(c.capacity : ℝ)*radialValue c.vector r/2)
      (fun r s t => -(c.weight : ℝ)*
        (radialValue c.vector s*tentProfile c.d r t +
          radialValue c.vector r*tentProfile c.d s t)/2) X = tentValue c X := by
  have hn : ∀ x ∈ X, x ≠ 0 := fun x hx he => hX (he ▸ hx)
  have hl : (∑ x ∈ X, (c.weight : ℝ)*(c.capacity : ℝ)*radialValue c.vector ‖x‖/2) =
      ∑ x ∈ X, (c.capacity : ℝ)*((c.weight : ℝ)*radialValue c.vector ‖x‖)/2 :=
    Finset.sum_congr rfl fun _ _ => by ring
  have hp : (∑ x ∈ X, ∑ y ∈ X, -(c.weight : ℝ)*
      (radialValue c.vector ‖y‖*tentProfile c.d ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) +
        radialValue c.vector ‖x‖*tentProfile c.d ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)))/2) =
      ∑ x ∈ X, ∑ y ∈ X, -((c.weight : ℝ)*radialValue c.vector ‖y‖*
        Components.capP ‖x+(c.d : ℝ) • dir y‖ +
        (c.weight : ℝ)*radialValue c.vector ‖x‖*
        Components.capP ‖y+(c.d : ℝ) • dir x‖)/2 := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    have he : ⟪x,y⟫/(‖x‖*‖y‖) = ⟪y,x⟫/(‖y‖*‖x‖) := by
      rw [real_inner_comm x y, mul_comm ‖x‖ ‖y‖]
    rw [tentProfile_coordinates c.d (hn x hx) (hn y hy), he,
      tentProfile_coordinates c.d (hn y hy) (hn x hx)]
    ring
  unfold radialEnergy
  rw [zero_add, hl, hp, weighted_usage_identity]
  rfl

theorem tents_energy_identity (X : Finset E4) (hX : (0 : E4) ∉ X) :
    tentsEnergy X = (tents.map fun c => tentValue c X).sum := by
  unfold tentsEnergy tentsLinear tentsCorrection
  have hz : (tents.map fun _ => (0 : ℝ)).sum = 0 := by simp
  rw [← hz]
  have hneg : ∀ r s t : ℝ,
      -(tents.map fun c => (c.weight : ℝ)*
        (radialValue c.vector s*tentProfile c.d r t +
          radialValue c.vector r*tentProfile c.d s t)/2).sum =
      (tents.map fun c => -(c.weight : ℝ)*
        (radialValue c.vector s*tentProfile c.d r t +
          radialValue c.vector r*tentProfile c.d s t)/2).sum := by
    intro r s t
    rw [List.sum_neg]
    simp only [List.map_map, Function.comp_def, neg_div, neg_mul]
  simp_rw [hneg]
  rw [radialEnergy_list]
  simp_rw [tent_component_identity _ _ hX]

theorem tent_data_ok : ∀ c ∈ tents,
    (0 : ℚ) ≤ c.weight ∧ (∀ q ∈ c.vector, 0 ≤ q) ∧
    (c.capacity = 1 ∨ c.d = 3/5 ∧ c.capacity = 44923461417477/62500000000000) := by
  decide +kernel

theorem tents_energy_nonneg {X : Finset E4} (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) : 0 ≤ tentsEnergy X := by
  have hn : ∀ x ∈ X, x ≠ 0 := by
    intro x hx he
    have h := hX.1 x hx
    rw [he, norm_zero] at h
    norm_num at h
  have h0 : (0 : E4) ∉ X := fun h => hn 0 h rfl
  rw [tents_energy_identity X h0]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hw, hv, hcap⟩ := tent_data_ok c hc
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · exact mul_nonneg (Rat.cast_nonneg.mpr hw) (radialValue_nonneg _ hv (hX.1 y hy) (hR y hy))
  · apply sub_nonneg.mpr
    rcases hcap with hcap | ⟨hd, hcap⟩
    · rw [hcap, Rat.cast_one]
      simpa only [sub_neg_eq_add] using Components.blichfeldt_translate X hX.2
        (-((c.d : ℝ) • dir y))
    · have hc' : ‖-((c.d : ℝ) • dir y)‖ = (3/5 : ℝ) := by
        rw [norm_neg, norm_smul, norm_dir (hn y hy), hd]
        norm_num
      have hb := Components.refined_tent_capacity X hX.2 hX.1
        (-((c.d : ℝ) • dir y)) hc'
      simpa only [sub_neg_eq_add, hcap, Rat.cast_div, Rat.cast_ofNat,
        Components.tentCapacity] using hb

end
end D4Bound.V7
