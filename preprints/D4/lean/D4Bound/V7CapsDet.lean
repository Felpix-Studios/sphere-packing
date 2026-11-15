import D4Bound.V7Caps

/-! Deterministic pointed probes, including the closed-ball boundary and
subtraction of the packing origin. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

theorem admissible_insert_zero {X : Finset E4} (hX : Admissible X) :
    Components.UnitSep (insert 0 X) := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with rfl | hx
  · have hy' : y ∈ X := (Finset.mem_insert.mp hy).resolve_left (Ne.symm hxy)
    simpa only [zero_sub, norm_neg] using hX.1 y hy'
  · rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [sub_zero] using hX.1 x hx
    · exact hX.2 x hx y hy hxy

/-- Bound the nonorigin centres in any closed ball with the cap's actual
probe radius. The origin is removed precisely when `d²<=a²`. -/
theorem cap_nonorigin_ball_count {c : Cap} (hc : CapValid c)
    {X : Finset E4} (hX : Admissible X) (p : E4) (hp : ‖p‖ = (c.d : ℝ)) :
    ((X.filter fun x => ‖x-p‖^2 ≤ (c.a2 : ℝ)).card : ℝ) ≤ (c.multiplicity : ℝ) := by
  obtain ⟨hd,ha,hσ,hσ',hw,hv,T,hMT,hT⟩ := hc
  let Z := (insert 0 X).filter fun x => ‖x-p‖^2 ≤ (c.a2 : ℝ)
  have hz : Components.UnitSep Z := (admissible_insert_zero hX).mono (Finset.filter_subset _ _)
  have ht : 2*((T.val : ℝ)+1)*(c.a2 : ℝ) < T.val ∨
      (5 ≤ T.val ∧ (c.a2 : ℝ) < 1/2) := by
    rcases hT with hT | ⟨h5,hT⟩
    · left; exact_mod_cast hT
    · right
      refine ⟨h5, ?_⟩
      have hh : (c.a2 : ℝ) < ((1/2 : ℚ) : ℝ) := Rat.cast_lt.mpr hT
      norm_num at hh ⊢
      exact hh
  have hcard := cap_closed_ball_count Z hz p (c.a2 : ℝ) (Rat.cast_nonneg.mpr ha) T.val ht
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have h0 : (0 : E4) ∉ X := by
    intro hx
    have h := hX.1 0 hx
    norm_num at h
  by_cases hin : c.d^2 ≤ c.a2
  · have hin' : ‖(0 : E4)-p‖^2 ≤ (c.a2 : ℝ) := by
      rw [zero_sub, norm_neg, hp]
      exact_mod_cast hin
    have he : Z = insert 0 (X.filter fun x => ‖x-p‖^2 ≤ (c.a2 : ℝ)) := by
      ext x
      simp only [Z, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx,hb⟩; exact hx.elim Or.inl (fun hx => Or.inr ⟨hx,hb⟩)
      · rintro (rfl | ⟨hx,hb⟩)
        · exact ⟨Or.inl rfl, hin'⟩
        · exact ⟨Or.inr hx,hb⟩
    rw [he, Finset.card_insert_of_notMem (fun h => h0 (Finset.mem_of_mem_filter _ h))] at hcard
    have hcard' : ((X.filter fun x => ‖x-p‖^2 ≤ (c.a2 : ℝ)).card : ℝ) + 1 ≤ T.val := by
      exact_mod_cast hcard
    rw [if_pos hin] at hMT
    have hm : (c.multiplicity : ℝ)+1 = T.val := by exact_mod_cast hMT
    linarith
  · have hin' : ¬ ‖(0 : E4)-p‖^2 ≤ (c.a2 : ℝ) := by
      rw [zero_sub, norm_neg, hp]
      exact_mod_cast hin
    have he : Z = X.filter fun x => ‖x-p‖^2 ≤ (c.a2 : ℝ) := by
      ext x
      simp only [Z, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx,hb⟩
        · exact (hin' hb).elim
        · exact ⟨hx,hb⟩
      · rintro ⟨hx,hb⟩; exact ⟨Or.inr hx,hb⟩
    rw [he] at hcard
    rw [if_neg hin, add_zero] at hMT
    have hm : (c.multiplicity : ℝ) = T.val := by exact_mod_cast hMT
    rw [hm]
    exact_mod_cast hcard

/-- At either deterministic pole the probability is the exact closed ball
indicator. No angular limiting convention is used at equality. -/
theorem capProbability_pole {c : Cap} (hd : 0 < (c.d : ℝ))
    (hσ : (c.sigma : ℝ)^2 = 1) {x y : E4} (hx : x ≠ 0) (hy : y ≠ 0) :
    capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) =
      if ‖x-((c.d : ℝ)*(c.sigma : ℝ)) • dir y‖^2 ≤ (c.a2 : ℝ) then 1 else 0 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hs : (1-(c.sigma : ℝ)^2)*(1-(⟪x,y⟫/(‖x‖*‖y‖))*(⟪x,y⟫/(‖x‖*‖y‖))) = 0 := by
    rw [hσ]; ring
  have hn : ‖x-((c.d : ℝ)*(c.sigma : ℝ)) • dir y‖^2 =
      ‖x‖^2+(c.d : ℝ)^2-2*(c.d : ℝ)*(c.sigma : ℝ)*(⟪x,y⟫/‖y‖) := by
    rw [norm_sub_sq_real, norm_smul, norm_dir hy, mul_one, Real.norm_eq_abs, sq_abs,
      mul_pow, hσ, mul_one, real_inner_smul_right, dir, real_inner_smul_right]
    field_simp
    <;> ring
  have he : ((‖x‖*‖x‖+(c.d : ℝ)^2-(c.a2 : ℝ))/(2*(c.d : ℝ)*‖x‖) -
      (c.sigma : ℝ)*(⟪x,y⟫/(‖x‖*‖y‖)) ≤ 0) ↔
      ‖x-((c.d : ℝ)*(c.sigma : ℝ)) • dir y‖^2 ≤ (c.a2 : ℝ) := by
    rw [hn]
    have heq : (‖x‖*‖x‖+(c.d : ℝ)^2-(c.a2 : ℝ))/(2*(c.d : ℝ)*‖x‖) -
        (c.sigma : ℝ)*(⟪x,y⟫/(‖x‖*‖y‖)) =
        (‖x‖^2+(c.d : ℝ)^2-2*(c.d : ℝ)*(c.sigma : ℝ)*(⟪x,y⟫/‖y‖)-(c.a2 : ℝ)) /
        (2*(c.d : ℝ)*‖x‖) := by
      field_simp
      <;> ring
    rw [heq, div_le_iff₀ (mul_pos (mul_pos (by norm_num) hd) hr)]
    simp only [zero_mul, sub_nonpos]
  unfold capProbability
  rw [if_pos hs]
  simp only [he]

end
end D4Bound.V7
