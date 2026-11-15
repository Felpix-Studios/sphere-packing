import D4Bound.V7CyclicPolynomialDef
import D4Bound.V7PairPolynomial
import D4Bound.V7CyclicUpper

/-! Interpretation of the homogeneous polynomial as the actual V7 terms.
Radial selectors and every signed spherical/count term are preserved. -/
namespace D4Bound.V7.CyclicPoly
noncomputable section
open Classical
set_option maxHeartbeats 0

lemma sum_map_mul_left {α : Type*} (L : List α) (f : α → ℝ) (t : ℝ) :
    (L.map fun a => t*f a).sum = t*(L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,ih]; ring

lemma eval_basis (p i : ℕ) (a : Poly) (r s d : ℝ) :
    eval (basis p i a) r s d = basisValue p i (eval a r s d) := by
  have hz : (1/(((basisIntervals.getD p (0,1)).2 : ℝ)-
      ((basisIntervals.getD p (0,1)).1 : ℝ))) *
      (eval a r s d + -((basisIntervals.getD p (0,1)).1 : ℝ)) =
      (eval a r s d-((basisIntervals.getD p (0,1)).1 : ℝ)) /
        (((basisIntervals.getD p (0,1)).2 : ℝ)-((basisIntervals.getD p (0,1)).1 : ℝ)) := by
    ring
  simp only [basis,basisValue,eval_scale,eval_fastMul,eval_fastPower,eval_fastAdd,
    eval_constant,Rat.cast_div,Rat.cast_one,Rat.cast_neg,Rat.cast_sub,Rat.cast_natCast]
  rw [hz]
  ring

lemma eval_radial (v : List ℚ) (p : ℕ) (a : Poly) (r s d : ℝ)
    (hp : radialPiece (eval a r s d) = p) :
    eval (radial v p a) r s d = radialValue v (eval a r s d) := by
  simp only [radial,radialValue,hp,eval_fastSum,List.map_map,Function.comp_def,
    eval_scale,eval_basis]

lemma eval_gramRadial (ell p q : ℕ) (a b : Poly) (r s d : ℝ)
    (hp : radialPiece (eval a r s d) = p) (hq : radialPiece (eval b r s d) = q) :
    eval (gramRadial ell p q a b) r s d =
      ((gramRays.getD ell []).map fun ray => (ray.weight : ℝ)*
        radialValue ray.vector (eval a r s d)*radialValue ray.vector (eval b r s d)).sum := by
  simp only [gramRadial,eval_fastSum,List.map_map,Function.comp_def,eval_scale,
    eval_fastMul,eval_radial _ p a r s d hp,eval_radial _ q b r s d hq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ray _
  ring

lemma eval_gramBlock (ell p q : ℕ) (hell : ell ≤ 18) (a b A B : Poly) (r s d : ℝ)
    (hp : radialPiece (eval a r s d) = p) (hq : radialPiece (eval b r s d) = q)
    (hB : eval B r s d ≠ 0) :
    eval (gramBlock ell p q a b A B) r s d = (eval B r s d)^18 *
      (zonal ell (eval A r s d/eval B r s d) *
        ((gramRays.getD ell []).map fun ray => (ray.weight : ℝ)*
          radialValue ray.vector (eval a r s d)*radialValue ray.vector (eval b r s d)).sum /
          (gramDenominator : ℝ)) := by
  rw [gramBlock,eval_scale,eval_fastMul,eval_clearedZonal 18 ell hell A B r s d hB,
    eval_gramRadial ell p q a b r s d hp hq]
  push_cast
  ring

lemma gram_degree_bound : gramRays.length ≤ 19 := by decide +kernel

theorem eval_gram (p q : ℕ) (a b A B : Poly) (r s d : ℝ)
    (hp : radialPiece (eval a r s d) = p) (hq : radialPiece (eval b r s d) = q)
    (hB : eval B r s d ≠ 0) :
    eval (gram p q a b A B) r s d = (eval B r s d)^18 *
      gramPair (eval a r s d) (eval b r s d) (eval A r s d/eval B r s d) := by
  simp only [gram,eval_fastSum,List.map_map,Function.comp_def,gramPair]
  rw [← sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ell hell
  have he : ell ≤ 18 := by have := List.mem_range.mp hell; have := gram_degree_bound; omega
  exact eval_gramBlock ell p q he a b A B r s d hp hq hB

lemma count_eq (c : CountPolynomial) (hc : c ∈ countPolynomials) {r s : ℝ}
    (hr1 : 1 ≤ r) (hr7 : r ≤ 7/4) (hs1 : 1 ≤ s) (hs7 : s ≤ 7/4) :
    (count c (radialPiece r) (radialPiece s) : ℝ) = countPair c r s := by
  simp only [count,countPair,Rat.cast_mul,PairPoly.rat_map_sum]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp only [Rat.cast_mul,PairPoly.indicator_flag _ (PairPoly.count_radii_valid c hc i hi) hr1 hr7,
    PairPoly.indicator_flag _ (PairPoly.count_radii_valid c hc j hj) hs1 hs7]

lemma conditional_eq {r s : ℝ}
    (hr1 : 1 ≤ r) (hr7 : r ≤ 7/4) (hs1 : 1 ≤ s) (hs7 : s ≤ 7/4) :
    (conditional (radialPiece r) (radialPiece s) : ℝ) = conditionalPair r s := by
  simp only [conditional,conditionalPair,PairPoly.rat_map_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  obtain ⟨hi,ho⟩ := PairPoly.conditional_radii_valid c hc
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_neg,Rat.cast_sub,Rat.cast_add,Rat.cast_ofNat,
    PairPoly.indicator_flag _ hi hr1 hr7,PairPoly.indicator_flag _ ho hr1 hr7,
    PairPoly.indicator_flag _ hi hs1 hs7,PairPoly.indicator_flag _ ho hs1 hs7]

lemma spherical_degree_bound : ∀ c ∈ sphericalRays, c.coefficients.length ≤ 19 := by
  decide +kernel

theorem eval_sphericalBlock (c : SphericalRay) (hc : c ∈ sphericalRays)
    (A B : Poly) (x y z r s : ℝ)
    (hr1 : 1 ≤ r) (hr7 : r ≤ 7/4) (hs1 : 1 ≤ s) (hs7 : s ≤ 7/4)
    (hB : eval B x y z ≠ 0) :
    eval (sphericalBlock c (radialPiece r) (radialPiece s) A B) x y z =
      (eval B x y z)^18 * (-(c.weight : ℝ)*indicator c.radius r*indicator c.radius s*
        ((List.range c.coefficients.length).map fun ell =>
          (c.coefficients.getD ell 0 : ℝ)*zonal ell (eval A x y z/eval B x y z)).sum) := by
  have hr := PairPoly.indicator_flag _ (PairPoly.spherical_radii_valid c hc) hr1 hr7
  have hs := PairPoly.indicator_flag _ (PairPoly.spherical_radii_valid c hc) hs1 hs7
  simp only [sphericalBlock,eval_fastSum,List.map_map,Function.comp_def,eval_scale]
  rw [hr,hs]
  rw [← mul_assoc,← sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ell hell
  have he : ell ≤ 18 := by
    have := List.mem_range.mp hell
    have := spherical_degree_bound c hc
    omega
  rw [eval_clearedZonal 18 ell he A B x y z hB]
  push_cast
  ring

theorem eval_spherical (A B : Poly) (x y z r s : ℝ)
    (hr1 : 1 ≤ r) (hr7 : r ≤ 7/4) (hs1 : 1 ≤ s) (hs7 : s ≤ 7/4)
    (hB : eval B x y z ≠ 0) :
    eval (spherical (radialPiece r) (radialPiece s) A B) x y z =
      (eval B x y z)^18 * sphericalPair r s (eval A x y z/eval B x y z) := by
  simp only [spherical,eval_fastSum,List.map_map,Function.comp_def,sphericalPair]
  rw [← sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  exact eval_sphericalBlock c hc A B x y z r s hr1 hr7 hs1 hs7 hB

theorem eval_pair (a b A B : Poly) (x y z : ℝ)
    (hr1 : 1 ≤ eval a x y z) (hr7 : eval a x y z ≤ 7/4)
    (hs1 : 1 ≤ eval b x y z) (hs7 : eval b x y z ≤ 7/4)
    (hB : eval B x y z ≠ 0) :
    eval (pair (radialPiece (eval a x y z)) (radialPiece (eval b x y z)) a b A B) x y z =
      (eval B x y z)^18 * polynomialPair (eval a x y z) (eval b x y z)
        (eval A x y z/eval B x y z) := by
  simp only [pair,eval_fastAdd,eval_scale,eval_fastPower,
    eval_gram _ _ a b A B x y z rfl rfl hB,
    eval_spherical A B x y z _ _ hr1 hr7 hs1 hs7 hB,Rat.cast_add,
    conditional_eq hr1 hr7 hs1 hs7,PairPoly.rat_map_sum]
  have hc : (countPolynomials.map fun c =>
      (count c (radialPiece (eval a x y z)) (radialPiece (eval b x y z)) : ℝ)).sum =
      (countPolynomials.map fun c => countPair c (eval a x y z) (eval b x y z)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    exact count_eq c hc hr1 hr7 hs1 hs7
  rw [hc]
  unfold polynomialPair
  ring

end
end D4Bound.V7.CyclicPoly

#print axioms D4Bound.V7.CyclicPoly.eval_pair
