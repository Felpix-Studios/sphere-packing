import D4Bound.V7CapsDet

/-! Concrete cap nonnegativity from the actual probability capacities.
The pole capacities are proved here without a measure-theoretic premise. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

/-- The only analytic input needed for a cap after its exact data and
closed-ball count have been checked. -/
def CapProbabilityCapacity (c : Cap) : Prop :=
  ∀ X : Finset E4, Admissible X → ∀ y : E4, y ≠ 0 →
    (∑ x ∈ X, capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖))) ≤ (c.multiplicity : ℝ)

theorem pole_cap_capacity {c : Cap} (hc : CapValid c)
    (hσ : c.sigma = -1 ∨ c.sigma = 1) : CapProbabilityCapacity c := by
  intro X hX y hy
  have hd : 0 < (c.d : ℝ) := Rat.cast_pos.mpr hc.1
  have hσ2 : (c.sigma : ℝ)^2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  let p : E4 := ((c.d : ℝ)*(c.sigma : ℝ)) • dir y
  have hp : ‖p‖ = (c.d : ℝ) := by
    dsimp [p]
    rw [norm_smul, norm_dir hy, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hd]
    have he : |(c.sigma : ℝ)| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    rw [he, mul_one]
  have hn : ∀ x ∈ X, x ≠ 0 := by
    intro x hx he
    have h := hX.1 x hx
    rw [he, norm_zero] at h
    norm_num at h
  have he : (∑ x ∈ X, capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖))) =
      ((X.filter fun x => ‖x-p‖^2 ≤ (c.a2 : ℝ)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    exact capProbability_pole hd hσ2 (hn x hx) hy
  rw [he]
  exact cap_nonorigin_ball_count hc hX p hp

theorem capValue_nonneg {c : Cap} (hc : CapValid c) (hcap : CapProbabilityCapacity c)
    {X : Finset E4} (hX : Admissible X) (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    0 ≤ capValue c X := by
  unfold capValue
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · exact mul_nonneg (Rat.cast_nonneg.mpr hc.2.2.2.2.1)
      (capWeight_nonneg hc (hX.1 y hy) (hR y hy))
  · apply sub_nonneg.mpr
    apply hcap X hX y
    intro he
    have h := hX.1 y hy
    rw [he, norm_zero] at h
    norm_num at h

/-- All59 deterministic cap energies, with the original weights and cutoffs. -/
def poleCaps : List Cap := caps.filter fun c => decide (c.sigma = -1 ∨ c.sigma = 1)

theorem poleCaps_length : poleCaps.length = 59 := by decide +kernel

theorem pole_caps_energy_nonneg {X : Finset E4} (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    0 ≤ (poleCaps.map fun c => capValue c X).sum := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  have hmem : c ∈ caps ∧ (c.sigma = -1 ∨ c.sigma = 1) := by
    simpa only [poleCaps, List.mem_filter, decide_eq_true_eq] using hc
  exact capValue_nonneg (caps_data_valid c hmem.1)
    (pole_cap_capacity (caps_data_valid c hmem.1) hmem.2) hX hR

/-- The full physical cap energy, conditional only on the remaining genuine
probability capacities; no radius or data assumptions are hidden. -/
theorem caps_energy_nonneg_of_capacities
    (hcap : ∀ c ∈ caps, CapProbabilityCapacity c)
    {X : Finset E4} (hX : Admissible X) (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    0 ≤ capsEnergy X := by
  rw [caps_energy_identity]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  exact capValue_nonneg (caps_data_valid c hc) (hcap c hc) hX hR

end
end D4Bound.V7
