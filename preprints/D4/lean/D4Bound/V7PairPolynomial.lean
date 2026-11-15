import D4Bound.V7PairUpper
import D4Bound.V7PairPolynomialDef

/-! Executable rational polynomial arithmetic used to connect the pair certificate
with the concrete kernel. Coefficients are in increasing degree order. -/
namespace D4Bound.V7.PairPoly
noncomputable def eval : Poly → ℝ → ℝ
  | [],_ => 0
  | a::p,x => a+x*eval p x

lemma eval_add (p q : Poly) (x : ℝ) : eval (add p q) x = eval p x+eval q x := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,ih,Rat.cast_add]; ring

lemma eval_scale (a : ℚ) (p : Poly) (x : ℝ) : eval (scale a p) x = a*eval p x := by
  induction p with
  | nil => simp [scale,eval]
  | cons b p ih => simp only [scale,List.map_cons,eval] at *; rw [Rat.cast_mul,ih]; ring

lemma eval_mul (p q : Poly) (x : ℝ) : eval (mul p q) x = eval p x*eval q x := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => simp only [mul,eval_add,eval_scale,eval,Rat.cast_zero,ih]; ring

lemma eval_pow (p : Poly) (n : ℕ) (x : ℝ) : eval (pow p n) x = eval p x^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => rw [pow,eval_mul,ih,pow_succ]

lemma eval_sum (ps : List Poly) (x : ℝ) : eval (sum ps) x = (ps.map fun p => eval p x).sum := by
  induction ps with
  | nil => simp [sum,eval]
  | cons p ps ih => simp only [sum,eval_add,ih,List.map_cons,List.sum_cons]

lemma eval_const (a : ℚ) (x : ℝ) : eval [a] x = a := by simp [eval]

lemma evalZ_cast (p : List ℤ) (x : ℝ) : eval (p.map Int.cast) x = D4Bound.evalZ p x := by
  induction p with
  | nil => simp [eval,D4Bound.evalZ]
  | cons a p ih => simp [eval,D4Bound.evalZ,ih]

noncomputable section
lemma eval_basis (p i : ℕ) (r : ℝ) : eval (basis p i) r = basisValue p i r := by
  have hz : eval [-((basisIntervals.getD p (0,1)).1) /
      ((basisIntervals.getD p (0,1)).2-(basisIntervals.getD p (0,1)).1),
      1/((basisIntervals.getD p (0,1)).2-(basisIntervals.getD p (0,1)).1)] r =
      (r-((basisIntervals.getD p (0,1)).1 : ℝ)) /
      (((basisIntervals.getD p (0,1)).2 : ℝ)-((basisIntervals.getD p (0,1)).1 : ℝ)) := by
    simp only [eval,Rat.cast_div,Rat.cast_sub,Rat.cast_neg,Rat.cast_one,mul_zero,add_zero]
    ring
  unfold basis basisValue
  simp only [eval_scale,eval_mul,eval_pow,eval_add,eval_const]
  rw [hz]
  push_cast
  ring

lemma eval_radial (v : List ℚ) (p : ℕ) (r : ℝ) (hp : radialPiece r = p) :
    eval (radial v p) r = radialValue v r := by
  unfold radial radialValue
  rw [eval_sum]
  simp only [List.map_map,Function.comp_def,eval_scale,eval_basis,hp]

end
end D4Bound.V7.PairPoly

namespace D4Bound.V7.PairPoly

noncomputable section
lemma indicator_flag (R : ℚ) (hR : R ∈ breaks.tail) {r : ℝ}
    (h1 : 1 ≤ r) (h7 : r ≤ 7/4) : indicator R r = (flag R (radialPiece r) : ℝ) := by
  norm_num [breaks] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [radialPiece_on_support h7] <;>
    split_ifs <;> norm_num [flag,breaks,indicator] at * <;> (try split_ifs) <;> linarith

lemma zonal_one (n : ℕ) : zonal n 1 = 1 := by
  rw [zonal_eq,Components.zfun,Polynomial.Chebyshev.U_eval_one]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  push_cast
  exact div_self hn

lemma eval_eq_evalQ (p : Poly) (r : ℝ) : eval p r = D4Bound.evalQ p r := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [eval,D4Bound.evalQ,ih]

lemma list_range_getD {α : Type*} (L : List α) (f : α → ℝ) (d : α) :
    ((List.range L.length).map fun i => f (L.getD i d)).sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons,List.range_succ_eq_map]
    simp only [List.map_cons,List.sum_cons,List.map_map,List.getD_cons_zero]
    simp only [Function.comp_def,List.getD_cons_succ,ih]

lemma list_sum_div (L : List ℝ) (d : ℝ) :
    L.sum/d = (L.map fun x => x/d).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [add_div,ih]

lemma rat_map_sum {α : Type*} (L : List α) (f : α → ℚ) :
    (((L.map f).sum : ℚ) : ℝ) = (L.map fun a : α => ((f a : ℚ) : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma rat_sum_cast_explicit (L : List ℚ) :
    ((L.sum : ℚ) : ℝ) = (L.map fun q : ℚ => (q : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma eval_gram (p : ℕ) (r : ℝ) (hp : radialPiece r = p) :
    eval (gram p) r = gramPair r r 1 := by
  unfold gram gramPair
  simp only [eval_sum,List.map_map,Function.comp_def,eval_scale,eval_mul,eval_radial _ p r hp,
    zonal_one,one_mul,Rat.cast_div]
  rw [list_range_getD gramRays
    (fun block : List Ray => (block.map fun ray =>
      (ray.weight : ℝ)*radialValue ray.vector r*radialValue ray.vector r).sum/(gramDenominator : ℝ)) []]
  apply congrArg List.sum
  apply List.map_congr_left
  intro block hb
  rw [list_sum_div]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ray hr
  ring

end
end D4Bound.V7.PairPoly

namespace D4Bound.V7.PairPoly
noncomputable section
open Classical

lemma count_radii_valid : ∀ c ∈ countPolynomials, ∀ i ∈ List.range c.radii.length,
    c.radii.getD i 0 ∈ breaks.tail := by decide +kernel
lemma spherical_radii_valid : ∀ c ∈ sphericalRays, c.radius ∈ breaks.tail := by decide +kernel
lemma conditional_radii_valid : ∀ c ∈ conditionalRays,
    c.inner ∈ breaks.tail ∧ c.outer ∈ breaks.tail := by decide +kernel

lemma countLin_eq (c : CountPolynomial) (hc : c ∈ countPolynomials) {r : ℝ}
    (h1 : 1 ≤ r) (h7 : r ≤ 7/4) : (countLin c (radialPiece r) : ℝ) = countLinear c r := by
  simp only [countLin,countLinear,Rat.cast_mul,rat_map_sum,List.map_map,Function.comp_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [Rat.cast_mul,indicator_flag _ (count_radii_valid c hc i hi) h1 h7]

lemma countDiag_eq (c : CountPolynomial) (hc : c ∈ countPolynomials) {r : ℝ}
    (h1 : 1 ≤ r) (h7 : r ≤ 7/4) : (countDiag c (radialPiece r) : ℝ) = countPair c r r := by
  simp only [countDiag,countPair,Rat.cast_mul,rat_map_sum,List.map_map,Function.comp_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp only [Rat.cast_mul,indicator_flag _ (count_radii_valid c hc i hi) h1 h7,
    indicator_flag _ (count_radii_valid c hc j hj) h1 h7]

lemma eval_uncut {r : ℝ} (h1 : 1 ≤ r) (h7 : r ≤ 7/4) :
    eval (uncut (radialPiece r)) r = uncutLinear r := by
  have hs : (((sphericalRays.map fun c => c.weight*c.bound*flag c.radius (radialPiece r)/2).sum : ℚ) : ℝ) =
      (sphericalRays.map fun c => (c.weight : ℝ)*(c.bound : ℝ)*indicator c.radius r/2).sum := by
    rw [rat_map_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    rw [indicator_flag _ (spherical_radii_valid c hc) h1 h7]
    push_cast
    rfl
  have hc : (((conditionalRays.map fun c => 23*c.weight*
      (flag c.outer (radialPiece r)-flag c.inner (radialPiece r))/2).sum : ℚ) : ℝ) =
      (conditionalRays.map fun c => 23*(c.weight : ℝ)*
        (indicator c.outer r-indicator c.inner r)/2).sum := by
    rw [rat_map_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    rw [indicator_flag _ (conditional_radii_valid c hc).1 h1 h7,
      indicator_flag _ (conditional_radii_valid c hc).2 h1 h7]
    push_cast
    rfl
  have hn : (((countPolynomials.map fun c => countLin c (radialPiece r)).sum : ℚ) : ℝ) =
      (countPolynomials.map fun c => countLinear c r).sum := by
    rw [rat_map_sum]
    apply congrArg List.sum
    exact List.map_congr_left fun c hc => countLin_eq c hc h1 h7
  unfold uncut uncutLinear
  simp only [eval_add,eval_scale,eval_sum,eval_const,eval_radial _ _ _ rfl,
    List.map_map,Function.comp_def,Rat.cast_add,hs,hc,hn]
  simp only [eval_scale,eval_radial _ _ _ rfl,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat]
  simp only [div_mul_eq_mul_div]
  ring

lemma sphericalDiag_eq {r : ℝ} (h1 : 1 ≤ r) (h7 : r ≤ 7/4) :
    (((sphericalRays.map fun c => -c.weight*flag c.radius (radialPiece r)*
      flag c.radius (radialPiece r)*c.coefficients.sum).sum : ℚ) : ℝ) = sphericalPair r r 1 := by
  unfold sphericalPair
  rw [rat_map_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  simp only [zonal_one,mul_one]
  rw [list_range_getD c.coefficients (fun q : ℚ => (q : ℝ)) 0]
  rw [indicator_flag _ (spherical_radii_valid c hc) h1 h7]
  simp only [Rat.cast_mul,Rat.cast_neg,rat_sum_cast_explicit]

lemma conditionalDiag_eq {r : ℝ} (h1 : 1 ≤ r) (h7 : r ≤ 7/4) :
    (((conditionalRays.map fun c => -c.weight*(flag c.inner (radialPiece r)*
      (flag c.outer (radialPiece r)-flag c.inner (radialPiece r))+
      (flag c.outer (radialPiece r)-flag c.inner (radialPiece r))*flag c.inner (radialPiece r))/2).sum : ℚ) : ℝ)
      = conditionalPair r r := by
  unfold conditionalPair
  rw [rat_map_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  rw [indicator_flag _ (conditional_radii_valid c hc).1 h1 h7,
    indicator_flag _ (conditional_radii_valid c hc).2 h1 h7]
  push_cast
  rfl

/-- The executable rational polynomial is the actual uncut diagonal upper. -/
theorem eval_diagonal {r : ℝ} (h1 : 1 ≤ r) (h7 : r ≤ 7/4) :
    eval (diagonal (radialPiece r)) r = diagonalUpper r := by
  have hn : (((countPolynomials.map fun c => countDiag c (radialPiece r)).sum : ℚ) : ℝ) =
      (countPolynomials.map fun c => countPair c r r).sum := by
    rw [rat_map_sum]
    apply congrArg List.sum
    exact List.map_congr_left fun c hc => countDiag_eq c hc h1 h7
  unfold diagonal diagonalUpper
  rw [eval_add,eval_scale,eval_uncut h1 h7,eval_add,eval_gram _ _ rfl,eval_const]
  simp only [Rat.cast_add,Rat.cast_ofNat]
  rw [sphericalDiag_eq h1 h7,conditionalDiag_eq h1 h7,hn]
  ring

end
end D4Bound.V7.PairPoly

namespace D4Bound.V7.PairPoly
noncomputable section

lemma eval_comp (p q : Poly) (r : ℝ) : eval (comp p q) r = eval p (eval q r) := by
  induction p with
  | nil => simp [comp,eval]
  | cons a p ih => simp only [comp,eval_add,eval_const,eval_mul,ih,eval,mul_zero,add_zero]

lemma list_range_sum (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

lemma eval_taylor (n : ℕ) (r : ℝ) :
    eval (taylor n) r = ∑ i ∈ Finset.range n, (2*r^2)^i / i.factorial := by
  unfold taylor
  rw [eval_sum]
  simp only [List.map_map,Function.comp_def,eval_scale,eval_pow]
  have h : eval [0,0,2] r = 2*r^2 := by simp [eval]; ring
  rw [list_range_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h]
  push_cast
  ring

end
end D4Bound.V7.PairPoly

namespace D4Bound.V7.PairPoly
noncomputable section

lemma eval_affine (a b : ℚ) (r : ℝ) (hab : a ≠ b) :
    eval [a,b-a] ((r-a)/(b-a)) = r := by
  have hn : (b : ℝ)-(a : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hab)
  simp only [eval,Rat.cast_sub,mul_zero,add_zero]
  field_simp
  ring

/-- Both endpoints belong to the actual radial cell selected by the kernel. -/
lemma radialPiece_interval {r : ℝ} (h1 : 1 ≤ r) (h7 : r ≤ 7/4) :
    ((breaks.getD (radialPiece r) 0 : ℚ) : ℝ) ≤ r ∧
      r ≤ ((breaks.getD (radialPiece r+1) 0 : ℚ) : ℝ) := by
  rw [radialPiece_on_support h7]
  split_ifs <;> norm_num [breaks] at * <;> constructor <;> linarith

end
end D4Bound.V7.PairPoly
