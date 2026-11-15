import D4Bound.V7Tents
import D4Bound.ComponentsBall

/-! The pointed-cap energy and exact closed-ball capacities for the V7 data.
The deterministic and averaged probe cases are kept distinct. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

/-- Exact rational contract for a pointed cap. `T` counts all packing centres,
including the distinguished origin when it lies in the closed probe ball. -/
def CapValid (c : Cap) : Prop :=
  0 < c.d ∧ 0 ≤ c.a2 ∧ -1 ≤ c.sigma ∧ c.sigma ≤ 1 ∧
  0 ≤ c.weight ∧ (∀ q ∈ c.vector, 0 ≤ q) ∧
  ∃ T : Fin 6, c.multiplicity + (if c.d^2 ≤ c.a2 then 1 else 0) = (T.val : ℚ) ∧
    (2*((T.val : ℚ)+1)*c.a2 < T.val ∨ (5 ≤ T.val ∧ c.a2 < 1/2))

theorem caps_data_valid : ∀ c ∈ caps, CapValid c := by
  unfold CapValid
  decide +kernel

theorem capWeight_nonneg {c : Cap} (hc : CapValid c) {r : ℝ}
    (h1 : 1 ≤ r) (hR : r ≤ 7/4) : 0 ≤ capWeight c r := by
  have hv := radialValue_nonneg c.vector hc.2.2.2.2.2.1 h1 hR
  unfold capWeight
  cases c.cutoff <;> simp only
  · exact hv
  · split_ifs <;> positivity

def capValue (c : Cap) (X : Finset E4) : ℝ :=
  ∑ y ∈ X, (c.weight : ℝ)*capWeight c ‖y‖ *
    ((c.multiplicity : ℝ) - ∑ x ∈ X,
      capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)))

theorem cap_component_identity (c : Cap) (X : Finset E4) :
    radialEnergy 0 (fun r => (c.weight : ℝ)*(c.multiplicity : ℝ)*capWeight c r/2)
      (fun r s t => -(c.weight : ℝ)*
        (capWeight c s*capProbability c r t + capWeight c r*capProbability c s t)/2) X =
      capValue c X := by
  have hl : (∑ x ∈ X, (c.weight : ℝ)*(c.multiplicity : ℝ)*capWeight c ‖x‖/2) =
      ∑ x ∈ X, (c.multiplicity : ℝ)*((c.weight : ℝ)*capWeight c ‖x‖)/2 :=
    Finset.sum_congr rfl fun _ _ => by ring
  have hp : (∑ x ∈ X, ∑ y ∈ X, -(c.weight : ℝ)*
      (capWeight c ‖y‖*capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) +
        capWeight c ‖x‖*capProbability c ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)))/2) =
      ∑ x ∈ X, ∑ y ∈ X, -((c.weight : ℝ)*capWeight c ‖y‖*
        capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) +
        (c.weight : ℝ)*capWeight c ‖x‖*
        capProbability c ‖y‖ (⟪y,x⟫/(‖y‖*‖x‖)))/2 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have he : ⟪x,y⟫/(‖x‖*‖y‖) = ⟪y,x⟫/(‖y‖*‖x‖) := by
      rw [real_inner_comm x y, mul_comm ‖x‖ ‖y‖]
    rw [he]
    ring
  unfold radialEnergy
  rw [zero_add, hl, hp, weighted_usage_identity]
  rfl

theorem caps_energy_identity (X : Finset E4) :
    capsEnergy X = (caps.map fun c => capValue c X).sum := by
  unfold capsEnergy capsLinear capsCorrection
  have hz : (caps.map fun _ => (0 : ℝ)).sum = 0 := by simp
  rw [← hz]
  have hneg : ∀ r s t : ℝ,
      -(caps.map fun c => (c.weight : ℝ)*
        (capWeight c s*capProbability c r t + capWeight c r*capProbability c s t)/2).sum =
      (caps.map fun c => -(c.weight : ℝ)*
        (capWeight c s*capProbability c r t + capWeight c r*capProbability c s t)/2).sum := by
    intro r s t
    rw [List.sum_neg]
    simp only [List.map_map, Function.comp_def, neg_div, neg_mul]
  simp_rw [hneg]
  rw [radialEnergy_list]
  simp_rw [cap_component_identity]

/-- A checked variance/strict-obtuse radius contract bounds a closed ball. -/
theorem cap_closed_ball_count (Z : Finset E4) (hZ : Components.UnitSep Z)
    (p : E4) (a : ℝ) (ha : 0 ≤ a) (T : ℕ)
    (hT : 2*((T : ℝ)+1)*a < T ∨ (5 ≤ T ∧ a < 1/2))
    (hb : ∀ x ∈ Z, ‖x-p‖^2 ≤ a) : Z.card ≤ T := by
  rcases hT with hT | ⟨h5,ha'⟩
  · have hinj : Set.InjOn (fun x : E4 => x-p) Z :=
      fun x _ y _ hxy => sub_left_inj.mp hxy
    have hs : Components.UnitSep (Z.image fun x => x-p) := by
      intro x hx y hy hxy
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
      have hn : x' ≠ y' := fun e => hxy (by rw [e])
      simpa only [sub_sub_sub_cancel_right] using hZ x' hx' y' hy' hn
    have hr : ∀ x ∈ Z.image (fun x => x-p), ‖x‖ ≤ Real.sqrt a := by
      intro x hx
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      exact (Real.le_sqrt (norm_nonneg _) ha).mpr (hb x' hx')
    have h := Components.card_le_of_ball _ hs (Real.sqrt a) T
      (by rwa [Real.sq_sqrt ha]) hr
    rwa [Finset.card_image_of_injOn hinj] at h
  · exact (Components.card_le_five_of_closed_ball Z hZ p a ha' hb).trans h5

end
end D4Bound.V7
