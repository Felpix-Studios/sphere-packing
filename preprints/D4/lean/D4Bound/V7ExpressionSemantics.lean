import D4Bound.V7Expression

namespace D4Bound.V7Expression
noncomputable section
open Classical
open Expr
set_option linter.unusedSimpArgs false

@[simp] theorem eval_num0 (xs) : eval xs (0 : Expr) = (0 : ℝ) := by
  change ((0 : ℚ) : ℝ) = (0 : ℝ)
  norm_num
@[simp] theorem eval_num1 (xs) : eval xs (1 : Expr) = (1 : ℝ) := by
  change ((1 : ℚ) : ℝ) = (1 : ℝ)
  norm_num
@[simp] theorem eval_num2 (xs) : eval xs (2 : Expr) = (2 : ℝ) := by
  change ((2 : ℚ) : ℝ) = (2 : ℝ)
  norm_num
@[simp] theorem eval_num4 (xs) : eval xs (4 : Expr) = (4 : ℝ) := by
  change ((4 : ℚ) : ℝ) = (4 : ℝ)
  norm_num
@[simp] theorem eval_num23 (xs) : eval xs (23 : Expr) = (23 : ℝ) := by
  change ((23 : ℚ) : ℝ) = (23 : ℝ)
  norm_num

@[simp] theorem eval_ifLE (xs) (a b c d : Expr) :
    eval xs (.ifLE a b c d) = if eval xs a ≤ eval xs b then eval xs c else eval xs d := rfl
@[simp] theorem eval_ifLT (xs) (a b c d : Expr) :
    eval xs (.ifLT a b c d) = if eval xs a < eval xs b then eval xs c else eval xs d := rfl
@[simp] theorem eval_ifEQ (xs) (a b c d : Expr) :
    eval xs (.ifEQ a b c d) = if eval xs a = eval xs b then eval xs c else eval xs d := rfl
@[simp] theorem eval_max (xs) (a b : Expr) :
    eval xs (.max a b) = max (eval xs a) (eval xs b) := rfl
@[simp] theorem eval_min (xs) (a b : Expr) :
    eval xs (.min a b) = min (eval xs a) (eval xs b) := rfl
@[simp] theorem eval_sqrt (xs) (a : Expr) : eval xs (.sqrt a) = Real.sqrt (eval xs a) := rfl
@[simp] theorem eval_exp (xs) (a : Expr) : eval xs (.exp a) = Real.exp (eval xs a) := rfl

@[simp] theorem eval_basisE (xs) (p i : ℕ) (r : Expr) :
    eval xs (basisE p i r) = V7.basisValue p i (eval xs r) := by
  simp only [basisE, V7.basisValue, eval_mul, eval_pow, eval_rat, eval_div, eval_sub,
    eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, Rat.cast_natCast]

@[simp] theorem eval_radialE (xs) (v : List ℚ) (p : ℕ) (r : Expr)
    (hp : V7.radialPiece (eval xs r) = p) :
    eval xs (radialE v p r) = V7.radialValue v (eval xs r) := by
  simp only [radialE, V7.radialValue, hp, eval_sum, List.map_map, Function.comp_def,
    eval_mul, eval_rat, eval_basisE]

@[simp] theorem eval_chebE (xs) (n : ℕ) (t : Expr) :
    eval xs (chebE n t) = V7.chebU n (eval xs t) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebE, V7.chebU]
  | one => simp [chebE, V7.chebU]
  | more n hn hn1 => simp only [chebE, V7.chebU, eval_sub, eval_mul, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, hn, hn1]

@[simp] theorem eval_zonalE (xs) (n : ℕ) (t : Expr) :
    eval xs (zonalE n t) = V7.zonal n (eval xs t) := by
  simp [zonalE, V7.zonal]

@[simp] theorem eval_indicatorE (xs) (R : ℚ) (r : Expr) :
    eval xs (indicatorE R r) = V7.indicator R (eval xs r) := by
  simp [indicatorE, V7.indicator]

@[simp] theorem eval_gramE (xs) (p q : ℕ) (r s t : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (gramE p q r s t) = V7.gramPair (eval xs r) (eval xs s) (eval xs t) := by
  simp only [gramE, V7.gramPair, eval_sum, List.map_map, Function.comp_def,
    eval_div, eval_mul, eval_rat, eval_zonalE, eval_radialE xs _ p r hp,
    eval_radialE xs _ q s hq]

@[simp] theorem eval_capWeightE (xs) (c : V7.Cap) (p : ℕ) (r : Expr)
    (hp : V7.radialPiece (eval xs r) = p) :
    eval xs (capWeightE c p r) = V7.capWeight c (eval xs r) := by
  unfold capWeightE V7.capWeight
  cases c.cutoff <;> simp only [eval_ifLT, eval_rat, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_radialE xs _ p r hp]

@[simp] theorem eval_capProbabilityE (xs) (c : V7.Cap) (r t : Expr) :
    eval xs (capProbabilityE c r t) = V7.capProbability c (eval xs r) (eval xs t) := by
  simp only [capProbabilityE, V7.capProbability, eval_ifEQ, eval_ifLE, eval_rat,
    eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_mul, eval_div, eval_sub, eval_add, eval_pow, eval_sqrt, eval_max, eval_min]

@[simp] theorem eval_capsE (xs) (p q : ℕ) (r s t : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (capsE p q r s t) = V7.capsCorrection (eval xs r) (eval xs s) (eval xs t) := by
  simp only [capsE, V7.capsCorrection, eval_sum, List.map_map, Function.comp_def,
    eval_div, eval_mul, eval_add, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_rat, eval_capProbabilityE,
    eval_capWeightE xs _ p r hp, eval_capWeightE xs _ q s hq]

@[simp] theorem eval_tentProfileE (xs) (d : ℚ) (r t : Expr) :
    eval xs (tentProfileE d r t) = V7.tentProfile d (eval xs r) (eval xs t) := by
  simp only [tentProfileE, V7.tentProfile, eval_max, eval_sub, eval_add, eval_mul,
    eval_rat, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23]

@[simp] theorem eval_tentsE (xs) (p q : ℕ) (r s t : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (tentsE p q r s t) = V7.tentsCorrection (eval xs r) (eval xs s) (eval xs t) := by
  simp only [tentsE, V7.tentsCorrection, eval_sum, List.map_map, Function.comp_def,
    eval_div, eval_mul, eval_add, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_rat, eval_tentProfileE,
    eval_radialE xs _ p r hp, eval_radialE xs _ q s hq]

@[simp] theorem eval_allocationProfileE (xs) (c : V7.AllocationData) (v : Expr) :
    eval xs (allocationProfileE c v) = V7.allocationProfile c (eval xs v) := by
  cases h : c.twoLevel <;>
    simp only [allocationProfileE, V7.allocationProfile, h, Bool.false_eq_true, Bool.true_eq,
      ite_false, ite_true, eval_ifLT, eval_ifLE, eval_div, eval_sub, eval_mul, eval_pow,
      eval_sqrt, eval_min, eval_rat, eval_num0, eval_num1, eval_num2, eval_num4]


@[simp] theorem eval_allocationsE (xs) (p q : ℕ) (r s t : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (allocationsE p q r s t) = V7.allocationsCorrection (eval xs r) (eval xs s) (eval xs t) := by
  simp only [allocationsE, V7.allocationsCorrection, eval_sum, List.map_map, Function.comp_def,
    eval_div, eval_mul, eval_add, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_rat, eval_allocationProfileE,
    eval_radialE xs _ p r hp, eval_radialE xs _ q s hq]

@[simp] theorem eval_conditionalE (xs) (r s : Expr) :
    eval xs (conditionalE r s) = V7.conditionalPair (eval xs r) (eval xs s) := by
  simp only [conditionalE, V7.conditionalPair, eval_sum, List.map_map, Function.comp_def,
    eval_div, eval_mul, eval_add, eval_sub, eval_neg, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_rat, eval_indicatorE]

@[simp] theorem eval_countPairE (xs) (c : V7.CountPolynomial) (r s : Expr) :
    eval xs (countPairE c r s) = V7.countPair c (eval xs r) (eval xs s) := by
  simp only [countPairE, V7.countPair, eval_sum, List.map_map, Function.comp_def,
    eval_mul, eval_rat, eval_indicatorE]

@[simp] theorem eval_sphericalE (xs) (r s t : Expr) :
    eval xs (sphericalE r s t) = V7.sphericalPair (eval xs r) (eval xs s) (eval xs t) := by
  simp only [sphericalE, V7.sphericalPair, eval_sum, List.map_map, Function.comp_def,
    eval_mul, eval_rat, eval_neg, eval_indicatorE, eval_zonalE]

@[simp] theorem eval_firstE (xs) (g : V7.Graph) (r : Expr) :
    eval xs (firstE g r) = if (g.lo1 : ℝ) ≤ eval xs r ∧ eval xs r ≤ (g.hi1 : ℝ) then 1 else 0 := by
  simp only [firstE, eval_ifLE, eval_rat, eval_num0, eval_num1]
  split_ifs <;> simp_all

@[simp] theorem eval_secondE (xs) (g : V7.Graph) (r : Expr) :
    eval xs (secondE g r) = if (if g.firstOpen then (g.lo2 : ℝ) < eval xs r else (g.lo2 : ℝ) ≤ eval xs r) ∧
        eval xs r ≤ (g.hi2 : ℝ) then 1 else 0 := by
  cases h : g.firstOpen <;>
    simp only [secondE, h, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
      eval_ifLE, eval_ifLT, eval_rat, eval_num0, eval_num1] <;>
    split_ifs <;> simp_all

@[simp] theorem eval_graphRadialE (xs) (g : V7.Graph) (r s : Expr) :
    eval xs (graphRadialE g r s) = if V7.graphRadial g (eval xs r) (eval xs s) then 1 else 0 := by
  by_cases h1 : (g.lo1 : ℝ) ≤ eval xs r ∧ eval xs r ≤ (g.hi1 : ℝ) <;>
  by_cases h2 : (if g.firstOpen then (g.lo2 : ℝ) < eval xs s else (g.lo2 : ℝ) ≤ eval xs s) ∧ eval xs s ≤ (g.hi2 : ℝ) <;>
  by_cases h3 : (g.lo1 : ℝ) ≤ eval xs s ∧ eval xs s ≤ (g.hi1 : ℝ) <;>
  by_cases h4 : (if g.firstOpen then (g.lo2 : ℝ) < eval xs r else (g.lo2 : ℝ) ≤ eval xs r) ∧ eval xs r ≤ (g.hi2 : ℝ) <;>
  cases hm : g.mixed <;>
  simp only [graphRadialE, V7.graphRadial, hm, Bool.false_eq_true, Bool.true_eq,
    ite_false, ite_true, branch, eval_ifEQ, eval_mul, eval_firstE, eval_secondE,
    eval_num1, h1, h2, h3, h4] <;> norm_num


@[simp] theorem eval_graphsE (xs) (r s t : Expr) :
    eval xs (graphsE r s t) = V7.graphsCorrection (eval xs r) (eval xs s) (eval xs t) := by
  simp only [graphsE, V7.graphsCorrection, eval_sum, List.map_map, Function.comp_def,
    branch, eval_ifEQ, eval_ifLE, eval_rat, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_graphRadialE]
  congr 1
  apply List.map_congr_left
  intro g hg
  split_ifs <;> simp_all

@[simp] theorem eval_rawPairE (xs) (p q : ℕ) (r s t : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (rawPairE p q r s t) = V7.rawPair (eval xs r) (eval xs s) (eval xs t) := by
  simp only [rawPairE, V7.rawPair, eval_sub, eval_add, eval_sum, List.map_map, Function.comp_def,
    eval_gramE xs p q r s t hp hq, eval_sphericalE, eval_conditionalE, eval_countPairE,
    eval_capsE xs p q r s t hp hq, eval_tentsE xs p q r s t hp hq,
    eval_allocationsE xs p q r s t hp hq, eval_graphsE]

@[simp] theorem eval_countLinearE (xs) (c : V7.CountPolynomial) (r : Expr) :
    eval xs (countLinearE c r) = V7.countLinear c (eval xs r) := by
  simp only [countLinearE, V7.countLinear, eval_sum, List.map_map, Function.comp_def,
    eval_mul, eval_rat, eval_indicatorE]

@[simp] theorem eval_rawLinearE (xs) (p : ℕ) (r : Expr)
    (hp : V7.radialPiece (eval xs r) = p) :
    eval xs (rawLinearE p r) = V7.rawLinear (eval xs r) := by
  simp only [rawLinearE, V7.rawLinear, eval_sum, List.map_map, Function.comp_def,
    eval_add, eval_sub, eval_mul, eval_div, eval_rat, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23,
    eval_radialE xs _ p r hp, eval_capWeightE xs _ p r hp, eval_indicatorE, eval_countLinearE]

@[simp] theorem eval_polyE (xs) (cs : List ℚ) (x : Expr) :
    eval xs (polyE cs x) = evalQ cs (eval xs x) := by
  induction cs with
  | nil => simp [polyE, evalQ]
  | cons c cs ih =>
    change eval xs (.rat c+x*polyE cs x) = _
    simp only [eval_add, eval_mul, eval_rat, ih, evalQ]

@[simp] theorem eval_scalarE (xs) (r : Expr) :
    eval xs (scalarE r) = V7.scalarRadius (eval xs r) := by
  simp only [scalarE, V7.scalarRadius, F, eval_mul, eval_exp, eval_neg, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_pow, eval_polyE]

@[simp] theorem eval_ungaugedE (xs) (p : ℕ) (r : Expr)
    (hp : V7.radialPiece (eval xs r) = p) :
    eval xs (ungaugedE p r) = V7.ungaugedPair (eval xs r) := by
  simp only [ungaugedE, V7.ungaugedPair, eval_add, eval_mul, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23, eval_scalarE,
    eval_rawLinearE xs p r hp, eval_rawPairE xs p p r r 1 hp hp]

@[simp] theorem eval_gaugePsiE (xs) (r : Expr) :
    eval xs (gaugePsiE r) = V7.gaugePsi (eval xs r) := by
  simp only [gaugePsiE, V7.gaugePsi, eval_div, eval_rat, eval_indicatorE]

@[simp] theorem eval_gaugeWeightE (xs) (p : ℕ) (r : Expr)
    (hp : V7.radialPiece (eval xs r) = p) :
    eval xs (gaugeWeightE p r) = V7.gaugeWeight (eval xs r) := by
  simp only [gaugeWeightE, V7.gaugeWeight, eval_div, eval_neg, eval_sub, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23,
    eval_ungaugedE xs p r hp, eval_gaugePsiE]

/-- Exact semantic bridge to the actual V7 pair; no sign certificate is assumed. -/
theorem eval_pairE (xs) (p q : ℕ) (r s t : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (pairE p q r s t) = V7.pair (eval xs r) (eval xs s) (eval xs t) := by
  simp only [pairE, V7.pair, eval_sub, eval_add, eval_div, eval_mul, eval_num0, eval_num1, eval_num2, eval_num4, eval_num23,
    eval_rawPairE xs p q r s t hp hq, eval_gaugeWeightE xs p r hp,
    eval_gaugeWeightE xs q s hq, eval_gaugePsiE]

end
end D4Bound.V7Expression
