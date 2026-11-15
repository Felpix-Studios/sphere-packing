import D4Bound.V7CyclicPolynomialFast

/-! Exact substitution for sparse polynomials. No sampled identity or
external coefficient-checking verdict is used in the real semantics. -/
namespace D4Bound.V7.CyclicPoly

def monomialPoly (e : Exponent) (a b c : Poly) : Poly :=
  fastMul (fastMul (fastPower a e.1) (fastPower b e.2.1)) (fastPower c e.2.2)

def compose (p a b c : Poly) : Poly :=
  fastSum (p.map fun t => scale t.2 (monomialPoly t.1 a b c))

theorem eval_monomialPoly (e : Exponent) (a b c : Poly) (r s d : ℝ) :
    eval (monomialPoly e a b c) r s d =
      monomial e (eval a r s d) (eval b r s d) (eval c r s d) := by
  simp only [monomialPoly,eval_fastMul,eval_fastPower,monomial]

theorem eval_compose (p a b c : Poly) (r s d : ℝ) :
    eval (compose p a b c) r s d =
      eval p (eval a r s d) (eval b r s d) (eval c r s d) := by
  simp only [compose,eval_fastSum,List.map_map,Function.comp_def,eval_scale,
    eval_monomialPoly]
  rfl

def affine (a b : ℚ) (i : Fin 3) : Poly :=
  fastAdd (constant a) (scale (b-a) (coordinate i))

theorem eval_affine0 (a b : ℚ) (r s d : ℝ) :
    eval (affine a b 0) r s d = (a : ℝ)+((b : ℝ)-(a : ℝ))*r := by
  simp only [affine,eval_fastAdd,eval_constant,eval_scale,eval_coordinate0,Rat.cast_sub]

theorem eval_affine1 (a b : ℚ) (r s d : ℝ) :
    eval (affine a b 1) r s d = (a : ℝ)+((b : ℝ)-(a : ℝ))*s := by
  simp only [affine,eval_fastAdd,eval_constant,eval_scale,eval_coordinate1,Rat.cast_sub]

theorem eval_affine2 (a b : ℚ) (r s d : ℝ) :
    eval (affine a b 2) r s d = (a : ℝ)+((b : ℝ)-(a : ℝ))*d := by
  simp only [affine,eval_fastAdd,eval_constant,eval_scale,eval_coordinate2,Rat.cast_sub]

theorem eval_affine_compose (p : Poly) (a b c d e f : ℚ) (x y z : ℝ) :
    eval (compose p (affine a b 0) (affine c d 1) (affine e f 2)) x y z =
      eval p ((a : ℝ)+((b : ℝ)-(a : ℝ))*x)
        ((c : ℝ)+((d : ℝ)-(c : ℝ))*y) ((e : ℝ)+((f : ℝ)-(e : ℝ))*z) := by
  rw [eval_compose,eval_affine0,eval_affine1,eval_affine2]

end D4Bound.V7.CyclicPoly

#print axioms D4Bound.V7.CyclicPoly.eval_affine_compose
