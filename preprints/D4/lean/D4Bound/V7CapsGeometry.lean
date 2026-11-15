import D4Bound.V7CapsNonneg

/-! Geometry of the transverse spherical probe; all boundary inequalities are closed. -/
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section

def capProbe (c : Cap) (e u : E4) : E4 :=
  (c.d : ℝ) • ((c.sigma : ℝ) • e + Real.sqrt (1-(c.sigma : ℝ)^2) • u)

def capTransverse (c : Cap) (v e : E4) : E4 :=
  Real.sqrt (1-(c.sigma : ℝ)^2) • (v - ⟪v,e⟫ • e)

theorem cap_sigma_sq_le {c : Cap} (hc : CapValid c) : (c.sigma : ℝ)^2 ≤ 1 := by
  have h1 : (-1 : ℝ) ≤ (c.sigma : ℝ) := by exact_mod_cast hc.2.2.1
  have h2 : (c.sigma : ℝ) ≤ 1 := by exact_mod_cast hc.2.2.2.1
  nlinarith

theorem capProbe_norm {c : Cap} (hc : CapValid c) {e u : E4}
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (heu : ⟪e,u⟫ = 0) :
    ‖capProbe c e u‖ = (c.d : ℝ) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr (cap_sigma_sq_le hc))
  have hn : ‖(c.sigma : ℝ) • e + Real.sqrt (1-(c.sigma : ℝ)^2) • u‖^2 = 1 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, he, hu,
      real_inner_smul_left, real_inner_smul_right, heu]
    simp only [mul_one, Real.norm_eq_abs, sq_abs, mul_zero, add_zero]
    nlinarith
  have hnorm : ‖(c.sigma : ℝ) • e + Real.sqrt (1-(c.sigma : ℝ)^2) • u‖ = 1 := by
    nlinarith [norm_nonneg ((c.sigma : ℝ) • e + Real.sqrt (1-(c.sigma : ℝ)^2) • u)]
  rw [capProbe, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_pos (Rat.cast_pos.mpr hc.1)]

theorem capTransverse_orthogonal (c : Cap) (v e : E4) (he : ‖e‖ = 1) :
    ⟪capTransverse c v e,e⟫ = 0 := by
  simp [capTransverse, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]

theorem capTransverse_norm_sq {c : Cap} (hc : CapValid c) {v e : E4}
    (hv : ‖v‖ = 1) (he : ‖e‖ = 1) :
    ‖capTransverse c v e‖^2 = (1-(c.sigma : ℝ)^2)*(1-⟪v,e⟫*⟪v,e⟫) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr (cap_sigma_sq_le hc))
  rw [capTransverse, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hs,
    norm_sub_sq_real, hv, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right]
  ring

theorem capProbe_distance {c : Cap} (hc : CapValid c) {x e u : E4}
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (heu : ⟪e,u⟫ = 0) :
    ‖x-capProbe c e u‖^2 = ‖x‖^2+(c.d : ℝ)^2 -
      2*(c.d : ℝ)*((c.sigma : ℝ)*⟪x,e⟫+Real.sqrt (1-(c.sigma : ℝ)^2)*⟪x,u⟫) := by
  rw [norm_sub_sq_real, capProbe_norm hc he hu heu]
  simp only [capProbe, real_inner_smul_right, inner_add_right]
  ring

theorem capProbe_membership {c : Cap} (hc : CapValid c) {x e u : E4}
    (hx : x ≠ 0) (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (heu : ⟪e,u⟫ = 0) :
    (‖x-capProbe c e u‖^2 ≤ (c.a2 : ℝ)) ↔
      (‖x‖*‖x‖+(c.d : ℝ)^2-(c.a2 : ℝ))/(2*(c.d : ℝ)*‖x‖) -
        (c.sigma : ℝ)*⟪dir x,e⟫ ≤ ⟪capTransverse c (dir x) e,u⟫ := by
  have hd : 0 < (c.d : ℝ) := Rat.cast_pos.mpr hc.1
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [capProbe_distance hc he hu heu]
  simp only [capTransverse, real_inner_smul_left, inner_sub_left, heu, mul_zero,
    sub_zero, dir, real_inner_smul_left]
  conv_rhs => rw [sub_le_iff_le_add, div_le_iff₀ (mul_pos (mul_pos (by norm_num) hd) hr)]
  field_simp
  constructor <;> intro h <;> nlinarith

end
end D4Bound.V7
