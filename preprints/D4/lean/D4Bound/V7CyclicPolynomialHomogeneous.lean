import D4Bound.V7CyclicPolynomialFast
import D4Bound.V7Kernel

/-! Homogeneous Chebyshev polynomials clear the side-cosine denominator.
The executable recurrence uses only rational polynomial operations. -/
namespace D4Bound.V7.CyclicPoly

def homogeneousU (A B : Poly) : ℕ → Poly
  | 0 => constant 1
  | 1 => scale 2 A
  | n+2 => fastAdd (scale 2 (fastMul A (homogeneousU A B (n+1))))
      (scale (-1) (fastMul (fastPower B 2) (homogeneousU A B n)))

theorem eval_homogeneousU (A B : Poly) (n : ℕ) (r s d : ℝ)
    (hB : eval B r s d ≠ 0) :
    eval (homogeneousU A B n) r s d =
      (eval B r s d)^n * chebU n (eval A r s d / eval B r s d) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [homogeneousU,chebU]
  | one =>
    simp only [homogeneousU,eval_scale,Rat.cast_ofNat,chebU,pow_one]
    field_simp [hB]
    <;> ring
  | more n hn hn1 =>
    simp only [homogeneousU,eval_fastAdd,eval_scale,eval_fastMul,eval_fastPower,
      Rat.cast_ofNat,Rat.cast_neg,hn,hn1,chebU,pow_succ]
    field_simp [hB]
    <;> ring

def clearedZonal (N n : ℕ) (A B : Poly) : Poly :=
  scale (1/(n+1 : ℚ)) (fastMul (fastPower B (N-n)) (homogeneousU A B n))

theorem eval_clearedZonal (N n : ℕ) (hn : n ≤ N) (A B : Poly) (r s d : ℝ)
    (hB : eval B r s d ≠ 0) :
    eval (clearedZonal N n A B) r s d =
      (eval B r s d)^N * zonal n (eval A r s d / eval B r s d) := by
  rw [clearedZonal,eval_scale,eval_fastMul,eval_fastPower,eval_homogeneousU A B n r s d hB]
  have hp : (eval B r s d)^(N-n)*(eval B r s d)^n = (eval B r s d)^N := by
    rw [← pow_add,Nat.sub_add_cancel hn]
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast,zonal]
  rw [← mul_assoc ((eval B r s d)^(N-n)) ((eval B r s d)^n),hp]
  ring

def sideNumerator (r s d : Poly) : Poly :=
  fastAdd (fastAdd (fastPower r 2) (fastPower s 2)) (scale (-1) (fastPower d 2))

def sideDenominator (r s : Poly) : Poly := scale 2 (fastMul r s)

@[simp] theorem eval_sideNumerator (a b c : Poly) (r s d : ℝ) :
    eval (sideNumerator a b c) r s d =
      (eval a r s d)^2+(eval b r s d)^2-(eval c r s d)^2 := by
  simp only [sideNumerator,eval_fastAdd,eval_fastPower,eval_scale,Rat.cast_neg,Rat.cast_one]
  ring

@[simp] theorem eval_sideDenominator (a b : Poly) (r s d : ℝ) :
    eval (sideDenominator a b) r s d = 2*eval a r s d*eval b r s d := by
  simp only [sideDenominator,eval_scale,eval_fastMul,Rat.cast_ofNat]
  ring

theorem side_factor_pos {r s d : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hd : 1 ≤ d) :
    0 < (2*r*s*d)^18 := by positivity

theorem exterior_factor_pos {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < (2*r*s)^18 := by positivity

end D4Bound.V7.CyclicPoly

#print axioms D4Bound.V7.CyclicPoly.eval_clearedZonal
