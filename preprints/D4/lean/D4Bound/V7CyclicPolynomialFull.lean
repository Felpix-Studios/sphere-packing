import D4Bound.V7CyclicPolynomialSemantics
import D4Bound.V7CyclicPolynomialSubstitution

/-! The exact positive normalization used by full triangle certificates. -/
namespace D4Bound.V7.CyclicPoly
noncomputable section

theorem full_factor_lower {r s d : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hd : 1 ≤ d) :
    (262144 : ℝ) ≤ (2*r*s*d)^18 := by
  have hrs : 1 ≤ r*s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs)]
  have hrsd : 1 ≤ r*s*d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (sub_nonneg.mpr hd)]
  have h : (2 : ℝ) ≤ 2*r*s*d := by nlinarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 18
  norm_num at hp
  exact hp

@[simp] theorem eval_fullFactor (a b c : Poly) (x y z : ℝ) :
    eval (fullFactor a b c) x y z = 2*eval a x y z*eval b x y z*eval c x y z := by
  simp only [fullFactor,eval_scale,eval_fastMul,Rat.cast_ofNat]
  ring

@[simp] theorem eval_fullNumerator (a b c : Poly) (x y z : ℝ) :
    eval (fullNumerator a b c) x y z =
      ((eval a x y z)^2+(eval b x y z)^2-(eval c x y z)^2)*eval c x y z := by
  simp only [fullNumerator,eval_fastMul,eval_sideNumerator]

theorem eval_cyclic (a b c : Poly) (x y z : ℝ)
    (hr1 : 1 ≤ eval a x y z) (hr7 : eval a x y z ≤ 7/4)
    (hs1 : 1 ≤ eval b x y z) (hs7 : eval b x y z ≤ 7/4)
    (hd1 : 1 ≤ eval c x y z) (hd7 : eval c x y z ≤ 7/4) :
    eval (cyclic (radialPiece (eval a x y z)) (radialPiece (eval b x y z))
      (radialPiece (eval c x y z)) a b c) x y z =
    (2*eval a x y z*eval b x y z*eval c x y z)^18 *
      polynomialSideCyclic (eval a x y z) (eval b x y z) (eval c x y z) := by
  have ha : eval a x y z ≠ 0 := by linarith
  have hb : eval b x y z ≠ 0 := by linarith
  have hc : eval c x y z ≠ 0 := by linarith
  have hB : eval (fullFactor a b c) x y z ≠ 0 := by
    rw [eval_fullFactor]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) hc
  have h0 : eval (fullNumerator a b c) x y z / eval (fullFactor a b c) x y z =
      sideCos (eval a x y z) (eval b x y z) (eval c x y z) := by
    rw [eval_fullNumerator,eval_fullFactor]
    unfold sideCos
    field_simp [ha,hb,hc]
    <;> ring
  have h1 : eval (fullNumerator a c b) x y z / eval (fullFactor a b c) x y z =
      sideCos (eval a x y z) (eval c x y z) (eval b x y z) := by
    rw [eval_fullNumerator,eval_fullFactor]
    unfold sideCos
    field_simp [ha,hb,hc]
    <;> ring
  have h2 : eval (fullNumerator b c a) x y z / eval (fullFactor a b c) x y z =
      sideCos (eval b x y z) (eval c x y z) (eval a x y z) := by
    rw [eval_fullNumerator,eval_fullFactor]
    unfold sideCos
    field_simp [ha,hb,hc]
    <;> ring
  simp only [cyclic,eval_fastAdd,
    eval_pair a b _ _ x y z hr1 hr7 hs1 hs7 hB,
    eval_pair a c _ _ x y z hr1 hr7 hd1 hd7 hB,
    eval_pair b c _ _ x y z hs1 hs7 hd1 hd7 hB]
  rw [h0,h1,h2,eval_fullFactor]
  unfold polynomialSideCyclic
  ring

theorem eval_full000 (r s d : ℝ)
    (hr1 : 1 ≤ r) (hr : r ≤ 501473/500000)
    (hs1 : 1 ≤ s) (hs : s ≤ 501473/500000)
    (hd1 : 1 ≤ d) (hd : d ≤ 501473/500000) :
    eval (cyclic 0 0 0 (coordinate 0) (coordinate 1) (coordinate 2)) r s d =
      (2*r*s*d)^18*polynomialSideCyclic r s d := by
  have hp : ∀ t : ℝ, t ≤ 501473/500000 → radialPiece t = 0 := by
    intro t ht
    simp [radialPiece,breaks,List.findIdx_cons,ht]
  have h := eval_cyclic (coordinate 0) (coordinate 1) (coordinate 2) r s d
    (by simpa using hr1) (by simpa using (show r ≤ 7/4 by linarith))
    (by simpa using hs1) (by simpa using (show s ≤ 7/4 by linarith))
    (by simpa using hd1) (by simpa using (show d ≤ 7/4 by linarith))
  simpa only [eval_coordinate0,eval_coordinate1,eval_coordinate2,hp r hr,hp s hs,hp d hd] using h

end
end D4Bound.V7.CyclicPoly

#print axioms D4Bound.V7.CyclicPoly.eval_full000
#print axioms D4Bound.V7.CyclicPoly.full_factor_lower
