import D4Bound.CyclicNativePoly
import D4Bound.V7CyclicPolynomialDef
import D4Bound.V7CyclicPolynomialSubstitution

/-!
# The native polynomial clone equals the original construction

On the actual V7 data `kdata`, `NPoly.cyclic kdata` is the function
`V7.CyclicPoly.cyclic`, and `NPoly.affine` is `V7.CyclicPoly.affine`.
-/
namespace D4Bound.CyclicNative.NPoly
open D4Bound.V7

def kdata : KData where
  breaks := breaks
  basisIntervals := basisIntervals
  gramRays := gramRays.map fun l => l.map fun r => (r.weight, r.vector)
  gramDenominator := gramDenominator
  conditionalRays := conditionalRays.map fun c => (c.inner, c.outer, c.weight)
  countPolynomials := countPolynomials.map fun c => (c.radii, c.weight, c.matrix)
  sphericalRays := sphericalRays.map fun c => (c.radius, c.weight, c.coefficients)

@[simp] lemma kdata_breaks : kdata.breaks = breaks := rfl
@[simp] lemma kdata_basisIntervals : kdata.basisIntervals = basisIntervals := rfl
@[simp] lemma kdata_gramRays : kdata.gramRays = gramRays.map fun l => l.map fun r => (r.weight, r.vector) := rfl
@[simp] lemma kdata_gramDenominator : kdata.gramDenominator = gramDenominator := rfl
@[simp] lemma kdata_conditionalRays :
    kdata.conditionalRays = conditionalRays.map fun c => (c.inner, c.outer, c.weight) := rfl
@[simp] lemma kdata_countPolynomials :
    kdata.countPolynomials = countPolynomials.map fun c => (c.radii, c.weight, c.matrix) := rfl
@[simp] lemma kdata_sphericalRays :
    kdata.sphericalRays = sphericalRays.map fun c => (c.radius, c.weight, c.coefficients) := rfl

theorem before_eq : @before = @CyclicPoly.before := rfl

theorem insert_eq : @insert = @CyclicPoly.insert := by
  funext t p
  induction p with
  | nil => rfl
  | cons u p ih => simp only [insert, CyclicPoly.insert, before_eq, ih]

theorem scale_eq : @scale = @CyclicPoly.scale := by
  funext a p; simp only [scale, CyclicPoly.scale, insert_eq]

theorem mulTerm_eq : @mulTerm = @CyclicPoly.mulTerm := rfl
theorem constant_eq : @constant = @CyclicPoly.constant := rfl
theorem coordinate_eq : @coordinate = @CyclicPoly.coordinate := rfl

theorem merge_eq : @merge = @CyclicPoly.merge := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext p q
    cases p with
    | nil => cases q <;> rfl
    | cons a p =>
      cases q with
      | nil => rfl
      | cons b q => simp only [merge, CyclicPoly.merge, before_eq, ih]

theorem fastAdd_eq : @fastAdd = @CyclicPoly.fastAdd := by
  funext p q; simp only [fastAdd, CyclicPoly.fastAdd, merge_eq]

theorem fastMul_eq : @fastMul = @CyclicPoly.fastMul := by
  funext p q; simp only [fastMul, CyclicPoly.fastMul, fastAdd_eq, mulTerm_eq]

theorem fastPower_eq : @fastPower = @CyclicPoly.fastPower := by
  funext p n
  induction n with
  | zero => rfl
  | succ n ih => simp only [fastPower, CyclicPoly.fastPower, fastMul_eq, ih]

theorem fastSum_eq : @fastSum = @CyclicPoly.fastSum := by
  funext ps; simp only [fastSum, CyclicPoly.fastSum, fastAdd_eq]

theorem homogeneousU_eq : @homogeneousU = @CyclicPoly.homogeneousU := by
  funext A B n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => simp only [homogeneousU, CyclicPoly.homogeneousU, scale_eq]
    | n+2 =>
      simp only [homogeneousU, CyclicPoly.homogeneousU, scale_eq, fastAdd_eq, fastMul_eq,
        fastPower_eq, ih n (by omega), ih (n+1) (by omega)]

theorem clearedZonal_eq : @clearedZonal = @CyclicPoly.clearedZonal := by
  funext N n A B
  simp only [clearedZonal, CyclicPoly.clearedZonal, scale_eq, fastMul_eq, fastPower_eq, homogeneousU_eq]

theorem sideNumerator_eq : @sideNumerator = @CyclicPoly.sideNumerator := by
  funext r s d
  simp only [sideNumerator, CyclicPoly.sideNumerator, scale_eq, fastAdd_eq, fastPower_eq]

theorem affine_eq : @affine = @CyclicPoly.affine := by
  funext a b i
  simp only [affine, CyclicPoly.affine, scale_eq, fastAdd_eq, constant_eq, coordinate_eq]

theorem pascal_getD (n : ℕ) : ∀ k, (pascal n).getD k 0 = n.choose k := by
  induction n with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [pascal]
    · simp [pascal]
  | succ n ih =>
    intro k
    by_cases hk : k < n+2
    · simp only [pascal]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hk, Option.getD_some]
      rcases k with _ | k
      · simp [ih 0]
      · simp only [Nat.add_sub_cancel, ih k, ih (k+1), Nat.choose_succ_succ', if_neg (Nat.succ_ne_zero k)]
        all_goals ring
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp only [pascal, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
      simp [hk]

theorem choose_eq (n k : ℕ) : choose n k = n.choose k := pascal_getD n k

theorem flag_eq : flag kdata = PairPoly.flag := rfl

theorem basis_eq : basis kdata = CyclicPoly.basis := by
  funext p i a
  simp only [basis, CyclicPoly.basis, kdata_basisIntervals, choose_eq, scale_eq, fastAdd_eq, fastMul_eq,
    fastPower_eq, constant_eq]

theorem radial_eq : radial kdata = CyclicPoly.radial := by
  funext v p a
  simp only [radial, CyclicPoly.radial, basis_eq, scale_eq, fastSum_eq]

lemma getD_map_nil {α β : Type*} (L : List (List α)) (g : α → β) (n : ℕ) :
    ((L.map fun l => l.map g).getD n []) = (L.getD n []).map g := by
  induction L generalizing n with
  | nil => simp
  | cons x L ih =>
    cases n with
    | zero => simp
    | succ n => simpa using ih n

theorem gramRadial_eq : gramRadial kdata = CyclicPoly.gramRadial := by
  funext ell p q a b
  simp only [gramRadial, CyclicPoly.gramRadial, kdata_gramRays, getD_map_nil, List.map_map,
    Function.comp_def, radial_eq, scale_eq, fastMul_eq, fastSum_eq]

theorem gramBlock_eq : gramBlock kdata = CyclicPoly.gramBlock := by
  funext ell p q a b A B
  simp only [gramBlock, CyclicPoly.gramBlock, gramRadial_eq, clearedZonal_eq, scale_eq, fastMul_eq]
  rfl

theorem gram_eq : gram kdata = CyclicPoly.gram := by
  funext p q a b A B
  simp only [gram, CyclicPoly.gram, gramBlock_eq, fastSum_eq, kdata_gramRays, List.length_map]

theorem conditional_eq : conditional kdata = CyclicPoly.conditional := by
  funext p q
  simp only [conditional, CyclicPoly.conditional, kdata_conditionalRays, List.map_map,
    Function.comp_def, flag_eq]

theorem count_eq (c : CountPolynomial) :
    count kdata (c.radii, c.weight, c.matrix) = CyclicPoly.count c := by
  funext p q
  simp only [count, CyclicPoly.count, flag_eq]

theorem sphericalBlock_eq (c : SphericalRay) :
    sphericalBlock kdata (c.radius, c.weight, c.coefficients) = CyclicPoly.sphericalBlock c := by
  funext p q A B
  simp only [sphericalBlock, CyclicPoly.sphericalBlock, flag_eq, scale_eq, clearedZonal_eq, fastSum_eq]

theorem spherical_eq : spherical kdata = CyclicPoly.spherical := by
  funext p q A B
  simp only [spherical, CyclicPoly.spherical, kdata_sphericalRays, List.map_map, Function.comp_def,
    sphericalBlock_eq, fastSum_eq]

theorem pair_eq : pair kdata = CyclicPoly.pair := by
  funext p q a b A B
  simp only [pair, CyclicPoly.pair, gram_eq, spherical_eq, conditional_eq, fastAdd_eq, scale_eq,
    fastPower_eq, kdata_countPolynomials, List.map_map, Function.comp_def, count_eq]

theorem cyclic_eq : cyclic kdata = CyclicPoly.cyclic := by
  funext p q k a b c
  simp only [cyclic, CyclicPoly.cyclic, pair_eq, fastAdd_eq, fullFactor, CyclicPoly.fullFactor,
    fullNumerator, CyclicPoly.fullNumerator, scale_eq, fastMul_eq, sideNumerator_eq]

end D4Bound.CyclicNative.NPoly

#print axioms D4Bound.CyclicNative.NPoly.cyclic_eq
#print axioms D4Bound.CyclicNative.NPoly.affine_eq
