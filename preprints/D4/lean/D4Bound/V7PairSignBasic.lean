import D4Bound.V7PairPolynomialTrimSound

/-! Soundness of normalized rational pair-sign certificates. -/
namespace D4Bound.V7
open PairPoly
noncomputable section

lemma pair_upper_sign_of_normalized (a b : ℚ) (hab : a < b) (D : PairPoly.Poly)
    (Z P : List ℤ) (DD PD : ℕ) (hDD : 0 < DD) (hPD : 0 < PD)
    (hD : PairPoly.trim (PairPoly.comp D [a,b-a]) =
      PairPoly.trim (PairPoly.scale (-1/(DD : ℚ)) (Z.map Int.cast)))
    (hP : PairPoly.trim (PairPoly.comp (PairPoly.add (PairPoly.comp Fq [0,0,2])
      (PairPoly.mul D (PairPoly.taylor 25))) [a,b-a]) =
      PairPoly.trim (PairPoly.scale (-1/(PD : ℚ)) (P.map Int.cast)))
    (hZ : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 < evalZ Z x)
    (hPP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 < evalZ P x)
    {r : ℝ} (ha : (a : ℝ) ≤ r) (hb : r ≤ (b : ℝ)) :
    scalarRadius r + PairPoly.eval D r ≤ 0 := by
  have hw : (0 : ℝ) < (b : ℝ)-(a : ℝ) := by exact_mod_cast sub_pos.mpr hab
  let x : ℝ := (r-a)/(b-a)
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr ha) hw.le
  have hx1 : x ≤ 1 := by apply (div_le_one hw).mpr; linarith
  have he : PairPoly.eval [a,b-a] x = r := PairPoly.eval_affine a b r (ne_of_lt hab)
  have hde := congrArg (fun q => PairPoly.eval q x) hD
  simp only [PairPoly.eval_trim,PairPoly.eval_comp,he,PairPoly.eval_scale,PairPoly.evalZ_cast] at hde
  have hdd : (0 : ℝ) < DD := Nat.cast_pos.mpr hDD
  have hpd : (0 : ℝ) < PD := Nat.cast_pos.mpr hPD
  have hdneg : PairPoly.eval D r ≤ 0 := by
    rw [hde]
    have hn : ((-1/(DD : ℚ) : ℚ) : ℝ) < 0 := by push_cast; exact div_neg_of_neg_of_pos (by norm_num) hdd
    exact le_of_lt (mul_neg_of_neg_of_pos hn (hZ x hx0 hx1))
  have hpe := congrArg (fun q => PairPoly.eval q x) hP
  simp only [PairPoly.eval_trim,PairPoly.eval_comp,he,PairPoly.eval_add,PairPoly.eval_mul,
    PairPoly.eval_scale,PairPoly.evalZ_cast,PairPoly.eval_taylor] at hpe
  have harg : PairPoly.eval [0,0,2] r = 2*r^2 := by simp [PairPoly.eval]; ring
  rw [harg,PairPoly.eval_eq_evalQ,← F] at hpe
  apply pair_sign_of_taylor r (PairPoly.eval D r) 25 hdneg
  rw [hpe]
  have hn : ((-1/(PD : ℚ) : ℚ) : ℝ) < 0 := by push_cast; exact div_neg_of_neg_of_pos (by norm_num) hpd
  exact le_of_lt (mul_neg_of_neg_of_pos hn (hPP x hx0 hx1))

end
end D4Bound.V7
