import D4Bound.V7ExpressionTargets

/-! Exact geometric reduction for the concrete V7 cyclic sign. This module
proves coordinate identities and domain coverage, not the certificate signs. -/
namespace D4Bound.V7
open scoped RealInnerProductSpace
noncomputable section

lemma negative_anchor_difference (x y : E4) : -x - (y-x) = -y := by abel

/-- The cosine at the vertex incident to sides r and s. -/
def sideCos (r s d : ℝ) : ℝ := (r^2+s^2-d^2)/(2*r*s)

def sideCyclic (r s d : ℝ) : ℝ :=
  pair r s (sideCos r s d) + pair r d (sideCos r d s) +
    pair s d (sideCos s d r)

lemma inner_sideCos {x y : E4} (hx : 0 < ‖x‖) (hy : 0 < ‖y‖) :
    ⟪x,y⟫/(‖x‖*‖y‖) = sideCos ‖x‖ ‖y‖ ‖x-y‖ := by
  unfold sideCos
  rw [norm_sub_sq_real]
  field_simp
  ring

lemma sideCyclic_kernel {x y : E4}
    (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) (hd : 1 ≤ ‖x-y‖)
    (hxr : ‖x‖ ≤ 7/4) (hyr : ‖y‖ ≤ 7/4) (hdr : ‖x-y‖ ≤ 7/4) :
    cyc kernel x y = sideCyclic ‖x‖ ‖y‖ ‖x-y‖ := by
  have hnx : 1 ≤ ‖-x‖ := by simpa using hx
  have hny : 1 ≤ ‖-y‖ := by simpa using hy
  have hdyx : 1 ≤ ‖y-x‖ := by simpa [norm_sub_rev] using hd
  have hxnr : ‖-x‖ ≤ 7/4 := by simpa using hxr
  have hynr : ‖-y‖ ≤ 7/4 := by simpa using hyr
  have hdyxr : ‖y-x‖ ≤ 7/4 := by simpa [norm_sub_rev] using hdr
  rw [cyc, V7Expression.kernel_eq_pair hx hy hxr hyr,
    V7Expression.kernel_eq_pair hnx hdyx hxnr hdyxr,
    V7Expression.kernel_eq_pair hny hd hynr hdr,
    inner_sideCos (by linarith) (by linarith),
    inner_sideCos (by linarith) (by linarith),
    inner_sideCos (by linarith) (by linarith)]
  simp only [negative_anchor_difference, norm_neg, norm_sub_rev y x]
  rfl

/-- The full symbolic target evaluates to the actual cyclic sum on supported triangles. -/
theorem triangle_expression_eq_cyclic {x y : E4}
    (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) (hd : 1 ≤ ‖x-y‖)
    (hxr : ‖x‖ ≤ 7/4) (hyr : ‖y‖ ≤ 7/4) (hdr : ‖x-y‖ ≤ 7/4) :
    V7Expression.Expr.eval (fun i => if i=0 then ‖x‖ else if i=1 then ‖y‖ else ‖x-y‖)
      (V7Expression.triangleSumExpr (radialPiece ‖x‖) (radialPiece ‖y‖)
        (radialPiece ‖x-y‖)) = cyc kernel x y := by
  rw [sideCyclic_kernel hx hy hd hxr hyr hdr]
  simp only [V7Expression.triangleSumExpr, V7Expression.Expr.eval_add]
  rw [V7Expression.eval_trianglePairExpr _ _ _ _ _ _ (by simp [V7Expression.Expr.eval]) (by simp [V7Expression.Expr.eval]),
    V7Expression.eval_trianglePairExpr _ _ _ _ _ _ (by simp [V7Expression.Expr.eval]) (by simp [V7Expression.Expr.eval]),
    V7Expression.eval_trianglePairExpr _ _ _ _ _ _ (by simp [V7Expression.Expr.eval]) (by simp [V7Expression.Expr.eval])]
  simp [V7Expression.Expr.eval, sideCyclic, sideCos]

/-- Exterior cases contain just the kernel rooted at the opposite vertex. -/
theorem cyclic_exterior_d {x y : E4} (hd : 7/4 < ‖x-y‖) :
    cyc kernel x y = kernel x y := by
  have h1 := kernel_supported (-x) (y-x) (Or.inr (by simpa [norm_sub_rev] using hd))
  have h2 := kernel_supported (-y) (x-y) (Or.inr hd)
  simp [cyc, h1, h2]

theorem cyclic_exterior_x {x y : E4} (hx : 7/4 < ‖x‖) :
    cyc kernel x y = kernel (-y) (x-y) := by
  have h0 := kernel_supported x y (Or.inl hx)
  have h1 := kernel_supported (-x) (y-x) (Or.inl (by simpa using hx))
  simp [cyc, h0, h1]

theorem cyclic_exterior_y {x y : E4} (hy : 7/4 < ‖y‖) :
    cyc kernel x y = kernel (-x) (y-x) := by
  have h0 := kernel_supported x y (Or.inr hy)
  have h2 := kernel_supported (-y) (x-y) (Or.inl (by simpa using hy))
  simp [cyc, h0, h2]

/-- Complete geometric interface for cyclic certificates. Exterior obligations
are only imposed on actual feasible side lengths, including degenerate triangles. -/
theorem cyclicSign_of_side_certificates
    (full : ∀ r s d : ℝ, 1 ≤ r → r ≤ 7/4 → 1 ≤ s → s ≤ 7/4 →
      1 ≤ d → d ≤ 7/4 → sideCyclic r s d ≤ 0)
    (outside : ∀ r s d : ℝ, 1 ≤ r → r ≤ 7/4 → 1 ≤ s → s ≤ 7/4 →
      7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) : CyclicSign kernel := by
  have single : ∀ a b : E4, 1 ≤ ‖a‖ → 1 ≤ ‖b‖ → 7/4 < ‖a-b‖ → kernel a b ≤ 0 := by
    intro a b ha hb hd
    by_cases har : ‖a‖ ≤ 7/4
    · by_cases hbr : ‖b‖ ≤ 7/4
      · rw [V7Expression.kernel_eq_pair ha hb har hbr, inner_sideCos (by linarith) (by linarith)]
        exact outside _ _ _ ha har hb hbr hd (norm_sub_le _ _)
      · rw [kernel_supported a b (Or.inr (lt_of_not_ge hbr))]
    · rw [kernel_supported a b (Or.inl (lt_of_not_ge har))]
  intro x y hx hy hd
  by_cases hxr : ‖x‖ ≤ 7/4
  · by_cases hyr : ‖y‖ ≤ 7/4
    · by_cases hdr : ‖x-y‖ ≤ 7/4
      · rw [sideCyclic_kernel hx hy hd hxr hyr hdr]
        exact full _ _ _ hx hxr hy hyr hd hdr
      · rw [cyclic_exterior_d (lt_of_not_ge hdr)]
        exact single x y hx hy (lt_of_not_ge hdr)
    · rw [cyclic_exterior_y (lt_of_not_ge hyr)]
      apply single (-x) (y-x) (by simpa using hx) (by simpa [norm_sub_rev] using hd)
      simpa only [negative_anchor_difference, norm_neg] using lt_of_not_ge hyr
  · rw [cyclic_exterior_x (lt_of_not_ge hxr)]
    apply single (-y) (x-y) (by simpa using hy) hd
    simpa only [negative_anchor_difference, norm_neg] using lt_of_not_ge hxr

#print axioms triangle_expression_eq_cyclic
#print axioms cyclicSign_of_side_certificates
end
end D4Bound.V7
