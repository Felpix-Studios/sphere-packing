import D4Bound.KernelBoxNativePoly
import D4Bound.V7PairUpper

/-!
# Polynomial mirrors of the smooth V7 kernel components

On a radial cell `(R_k, R_{k+1}]` (closed at `1` for `k = 0`) every radial feature of the
concrete kernel `V7.kernel` is a polynomial in `u = r - 1`, and every radial indicator is
constant. This module builds those polynomials with the executable algebra of
`KernelBoxNativePoly` and proves that they evaluate to the actual definitions in
`V7Kernel.lean`. It also builds a polynomial upper bound `Upoly k` for the full ungauged
diagonal source of the gauge, from any polynomial upper bound `ghat` of `scalarRadius`.
-/

namespace D4Bound.KBN
open V7

/-- The smooth part of `rawPair` (same as `CertificateInterval.pairCore`). -/
noncomputable def corePair (r s t : ℝ) : ℝ := gramPair r s t + sphericalPair r s t +
  conditionalPair r s + (countPolynomials.map fun c => countPair c r s).sum

/-! ## Radial cells and indicators -/

def cellLo (k : ℕ) : ℚ := breaks.getD k 1
def cellHi (k : ℕ) : ℚ := breaks.getD (k + 1) 1

/-- The radial cell `k`: `(R_k, R_{k+1}]`, closed at the bottom when `k = 0`. -/
def InCell (k : ℕ) (r : ℝ) : Prop :=
  (cellLo k : ℝ) ≤ r ∧ r ≤ (cellHi k : ℝ) ∧ (0 < k → (cellLo k : ℝ) < r)

def indQ (k : ℕ) (R : ℚ) : ℚ := if cellHi k ≤ R then 1 else 0

def indOK (k : ℕ) (R : ℚ) : Bool :=
  decide (cellHi k ≤ R) || decide (R < cellLo k) || (decide (0 < k) && decide (R ≤ cellLo k))

theorem indicator_cell {k : ℕ} {R : ℚ} (hok : indOK k R = true) {r : ℝ} (hr : InCell k r) :
    indicator R r = (indQ k R : ℝ) := by
  unfold indicator indQ
  obtain ⟨h1, h2, h3⟩ := hr
  simp only [indOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  by_cases hH : cellHi k ≤ R
  · have : r ≤ (R : ℝ) := le_trans h2 (by exact_mod_cast hH)
    simp [hH, this]
  · have hlt : (R : ℝ) < r := by
      rcases hok with (h | h) | ⟨hk, h⟩
      · exact absurd h hH
      · exact lt_of_lt_of_le (by exact_mod_cast h) h1
      · exact lt_of_le_of_lt (by exact_mod_cast h) (h3 hk)
    simp [hH, not_le.mpr hlt]

/-- Every radius used by an indicator of the smooth kernel. -/
def allRadii : List ℚ :=
  gaugeRadius :: (sphericalRays.map (·.radius) ++
    conditionalRays.flatMap (fun c => [c.inner, c.outer]) ++
    countPolynomials.flatMap (fun c => (List.range c.radii.length).map fun i => c.radii.getD i 0))

def cellOK (k : ℕ) : Bool := allRadii.all (indOK k)

theorem ind_of_mem {k : ℕ} (hk : cellOK k = true) {r : ℝ} (hr : InCell k r) {R : ℚ}
    (hR : R ∈ allRadii) : indicator R r = (indQ k R : ℝ) :=
  indicator_cell (List.all_eq_true.mp hk R hR) hr

theorem cast_sum_map {α : Type} (L : List α) (f : α → ℚ) :
    (((L.map f).sum : ℚ) : ℝ) = (L.map fun a => (f a : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-! ## Radial features -/

def bA (k : ℕ) : ℚ := (basisIntervals.getD k (0, 1)).1
def bB (k : ℕ) : ℚ := (basisIntervals.getD k (0, 1)).2

def zP (k : ℕ) : P1 := [(1 - bA k) / (bB k - bA k), 1 / (bB k - bA k)]
def omP (k : ℕ) : P1 := A1.add [1] (A1.smul (-1) (zP k))
def basisP (k i : ℕ) : P1 :=
  A1.smul (Nat.choose 6 i : ℚ) (A1.mul (ppow qAlg (zP k) i) (ppow qAlg (omP k) (6 - i)))
def rvP (v : List ℚ) (k : ℕ) : P1 :=
  psum qAlg ((List.range 7).map fun i => A1.smul (v.getD (7 * k + i) 0) (basisP k i))

theorem E1_zP {k : ℕ} (hk : k < 7) (r : ℝ) :
    E1 (zP k) (r - 1) = (r - (bA k : ℝ)) / ((bB k : ℝ) - (bA k : ℝ)) := by
  have hw : (0 : ℝ) < (bB k : ℝ) - (bA k : ℝ) := basis_width_pos hk
  have hw' : (bB k : ℝ) - (bA k : ℝ) ≠ 0 := hw.ne'
  simp only [zP, E1, peval_cons, peval_nil]
  push_cast
  field_simp
  ring

theorem E1_rvP (v : List ℚ) {r : ℝ} {k : ℕ} (hk : radialPiece r = k) (hk7 : k < 7) :
    E1 (rvP v k) (r - 1) = radialValue v r := by
  unfold radialValue rvP
  rw [hk, E1_psum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, E1_smul, basisP, E1_mul, E1_ppow, omP, E1_add, E1_zP hk7,
    E1_singleton]
  simp only [basisValue, bA, bB]
  push_cast
  ring

/-! ## Zonal functions -/

def chebPair : ℕ → P1 × P1
  | 0 => ([1], [0, 2])
  | n + 1 => ((chebPair n).2, A1.add (A1.mul [0, 2] (chebPair n).2) (A1.smul (-1) (chebPair n).1))

def zonalP (n : ℕ) : P1 := A1.smul (1 / ((n : ℚ) + 1)) (chebPair n).1

theorem E1_chebPair (t : ℝ) : ∀ n : ℕ,
    E1 (chebPair n).1 t = chebU n t ∧ E1 (chebPair n).2 t = chebU (n + 1) t
  | 0 => by
    constructor <;> simp only [chebPair, chebU, E1, peval_cons, peval_nil] <;> push_cast <;> ring
  | n + 1 => by
    obtain ⟨h1, h2⟩ := E1_chebPair t n
    refine ⟨h2, ?_⟩
    have h02 : E1 [0, 2] t = 2 * t := by
      simp only [E1, peval_cons, peval_nil]; push_cast; ring
    simp only [chebPair, E1_add, E1_mul, E1_smul, h1, h2, h02]
    simp only [chebU]
    push_cast
    ring

theorem E1_zonalP (n : ℕ) (t : ℝ) : E1 (zonalP n) t = zonal n t := by
  simp only [zonalP, E1_smul, (E1_chebPair t n).1, zonal]
  push_cast
  ring

/-! ## The smooth core `pairCore` -/

def gramP (kr ks : ℕ) : P3 :=
  psum A2 ((List.range gramRays.length).map fun l =>
    A3.smul (1 / gramDenominator) (A3.mul (liftT (zonalP l))
      (psum A2 ((gramRays.getD l []).map fun ray =>
        A3.smul ray.weight (A3.mul (liftU (rvP ray.vector kr)) (liftV (rvP ray.vector ks)))))))

def sphP (kr ks : ℕ) : P3 :=
  psum A2 (sphericalRays.map fun c =>
    A3.smul (-c.weight * indQ kr c.radius * indQ ks c.radius)
      (liftT (psum qAlg ((List.range c.coefficients.length).map fun j =>
        A1.smul (c.coefficients.getD j 0) (zonalP j)))))

def condQ (kr ks : ℕ) : ℚ :=
  (conditionalRays.map fun c => -c.weight *
    (indQ kr c.inner * (indQ ks c.outer - indQ ks c.inner) +
      (indQ kr c.outer - indQ kr c.inner) * indQ ks c.inner) / 2).sum

def countQ (kr ks : ℕ) : ℚ :=
  (countPolynomials.map fun c => c.weight * ((List.range c.radii.length).map fun i =>
    ((List.range c.radii.length).map fun j =>
      ((c.matrix.getD i []).getD j 0) * indQ kr (c.radii.getD i 0) *
        indQ ks (c.radii.getD j 0)).sum).sum).sum

def coreP (kr ks : ℕ) : P3 :=
  A3.add (gramP kr ks) (A3.add (sphP kr ks) (const3 (condQ kr ks + countQ kr ks)))

/-- Hypotheses on a pair of cells used by every component lemma. -/
structure CellPair (kr ks : ℕ) (r s : ℝ) : Prop where
  hr : InCell kr r
  hs : InCell ks s
  pr : radialPiece r = kr
  ps : radialPiece s = ks
  kr7 : kr < 7
  ks7 : ks < 7
  okr : cellOK kr = true
  oks : cellOK ks = true

theorem E3_gramP {kr ks : ℕ} {r s : ℝ} (h : CellPair kr ks r s) (t : ℝ) :
    E3 (gramP kr ks) (r - 1) (s - 1) t = gramPair r s t := by
  unfold gramP gramPair
  rw [E3_psum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l _
  simp only [Function.comp, E3_smul, E3_mul, E3_liftT, E1_zonalP, E3_psum, List.map_map]
  have hin : ((gramRays.getD l []).map fun ray =>
      E3 (A3.smul ray.weight (A3.mul (liftU (rvP ray.vector kr)) (liftV (rvP ray.vector ks))))
        (r - 1) (s - 1) t) =
      ((gramRays.getD l []).map fun ray =>
        (ray.weight : ℝ) * radialValue ray.vector r * radialValue ray.vector s) := by
    apply List.map_congr_left
    intro ray _
    simp only [E3_smul, E3_mul, E3_liftU, E3_liftV, E1_rvP _ h.pr h.kr7, E1_rvP _ h.ps h.ks7]
    ring
  simp only [Function.comp_def] at hin ⊢
  rw [hin]
  push_cast
  ring

theorem E3_sphP {kr ks : ℕ} {r s : ℝ} (h : CellPair kr ks r s) (t : ℝ) :
    E3 (sphP kr ks) (r - 1) (s - 1) t = sphericalPair r s t := by
  unfold sphP sphericalPair
  rw [E3_psum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  have hR : c.radius ∈ allRadii := by
    simp only [allRadii, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl (Or.inl ⟨c, hc, rfl⟩))
  simp only [Function.comp, E3_smul, E3_liftT, E1_psum, List.map_map,
    ind_of_mem h.okr h.hr hR, ind_of_mem h.oks h.hs hR]
  have hz : ((List.range c.coefficients.length).map fun j =>
      E1 (A1.smul (c.coefficients.getD j 0) (zonalP j)) t) =
      ((List.range c.coefficients.length).map fun j =>
        ((c.coefficients.getD j 0 : ℚ) : ℝ) * zonal j t) := by
    apply List.map_congr_left
    intro j _
    rw [E1_smul, E1_zonalP]
  simp only [Function.comp_def] at hz ⊢
  rw [hz]
  push_cast
  ring

theorem cond_eq {kr ks : ℕ} {r s : ℝ} (h : CellPair kr ks r s) :
    conditionalPair r s = (condQ kr ks : ℝ) := by
  unfold conditionalPair condQ
  rw [cast_sum_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  have hi : c.inner ∈ allRadii := by
    simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inl (Or.inr ⟨c, hc, by simp⟩))
  have ho : c.outer ∈ allRadii := by
    simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inl (Or.inr ⟨c, hc, by simp⟩))
  rw [ind_of_mem h.okr h.hr hi, ind_of_mem h.okr h.hr ho, ind_of_mem h.oks h.hs hi,
    ind_of_mem h.oks h.hs ho]
  push_cast; ring

theorem count_eq {kr ks : ℕ} {r s : ℝ} (h : CellPair kr ks r s) :
    (countPolynomials.map fun c => countPair c r s).sum = (countQ kr ks : ℝ) := by
  unfold countQ countPair
  rw [cast_sum_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  rw [Rat.cast_mul, cast_sum_map]
  apply congrArg (fun x => (c.weight : ℝ) * x)
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [cast_sum_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hRi : c.radii.getD i 0 ∈ allRadii := by
    simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inr ⟨c, hc, i, hi, rfl⟩)
  have hRj : c.radii.getD j 0 ∈ allRadii := by
    simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inr ⟨c, hc, j, hj, rfl⟩)
  rw [ind_of_mem h.okr h.hr hRi, ind_of_mem h.oks h.hs hRj]
  push_cast; ring

theorem E3_coreP {kr ks : ℕ} {r s : ℝ} (h : CellPair kr ks r s) (t : ℝ) :
    E3 (coreP kr ks) (r - 1) (s - 1) t = corePair r s t := by
  unfold coreP corePair
  rw [E3_add, E3_add, E3_const3, E3_gramP h, E3_sphP h, cond_eq h, count_eq h]
  push_cast
  ring

/-! ## Diagonal restriction `(u, u, 1)` -/

def diag3 (p : P3) : P1 :=
  horner A1 (fun q : P2 => horner A1 (fun c : P1 => [c.sum]) [0, 1] q) [0, 1] p

theorem E1_sum_one (c : P1) : E1 c 1 = (c.sum : ℝ) := by
  induction c with
  | nil => simp [E1]
  | cons a c ih =>
    simp only [E1, peval_cons, List.sum_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem E1_X (x : ℝ) : E1 [0, 1] x = x := by simp [E1]

theorem E1_diag3 (p : P3) (x : ℝ) : E1 (diag3 p) x = E3 p x x 1 := by
  unfold diag3 E3
  rw [eval_horner (M1 x) _ (ev := fun q : P2 => E2 q x 1), E1_X]
  intro q
  unfold E2
  rw [eval_horner (M1 x) _ (ev := fun c : P1 => E1 c 1), E1_X]
  intro c
  rw [E1_singleton, E1_sum_one]

/-! ## The ungauged diagonal source -/

/-- `capWeight` on a cell: the cut-off factor and its decidability. -/
def capCut (k : ℕ) (c : Cap) : ℚ :=
  match c.cutoff with
  | none => 1
  | some C => if cellHi k ≤ C then 0 else 1

def capCutOK (k : ℕ) (c : Cap) : Bool :=
  match c.cutoff with
  | none => true
  | some C => indOK k C

theorem capWeight_cell {k : ℕ} {c : Cap} (hok : capCutOK k c = true) {r : ℝ}
    (hr : InCell k r) : capWeight c r = (capCut k c : ℝ) * radialValue c.vector r := by
  unfold capWeight capCut
  unfold capCutOK at hok
  cases hC : c.cutoff with
  | none => simp
  | some C =>
    rw [hC] at hok
    simp only at hok ⊢
    have hi := indicator_cell hok hr
    unfold indicator indQ at hi
    by_cases h1 : cellHi k ≤ C
    · have : ¬ (C : ℝ) < r := not_lt.mpr (le_trans hr.2.1 (by exact_mod_cast h1))
      simp [h1, this]
    · have : (C : ℝ) < r := by
        by_contra hc
        have := not_lt.mp hc
        simp [h1, this] at hi
      simp [h1, this]

def capsCutOK (k : ℕ) : Bool := caps.all (capCutOK k)

def linP (k : ℕ) : P1 :=
  A1.add (rvP originVector k) (A1.add
    (psum qAlg (caps.map fun c => A1.smul (c.weight * c.multiplicity * capCut k c / 2) (rvP c.vector k)))
    (A1.add (psum qAlg (tents.map fun c => A1.smul (c.weight * c.capacity / 2) (rvP c.vector k)))
      (A1.add (psum qAlg (allocations.map fun c => A1.smul (c.weight / 2) (rvP c.vector k)))
        [(sphericalRays.map fun c => c.weight * c.bound * indQ k c.radius / 2).sum +
         (conditionalRays.map fun c => 23 * c.weight * (indQ k c.outer - indQ k c.inner) / 2).sum +
         (countPolynomials.map fun c => c.weight * ((List.range c.radii.length).map fun i =>
            c.linear.getD i 0 * indQ k (c.radii.getD i 0)).sum).sum])))

structure CellOne (k : ℕ) (r : ℝ) : Prop where
  hr : InCell k r
  pr : radialPiece r = k
  k7 : k < 7
  ok : cellOK k = true
  cut : capsCutOK k = true

theorem E1_linP {k : ℕ} {r : ℝ} (h : CellOne k r) : E1 (linP k) (r - 1) = rawLinear r := by
  unfold linP rawLinear
  simp only [E1_add, E1_psum, List.map_map, E1_singleton]
  simp only [Function.comp_def]
  rw [E1_rvP _ h.pr h.k7]
  have hc : ((caps.map fun c => E1 (A1.smul (c.weight * c.multiplicity * capCut k c / 2)
      (rvP c.vector k)) (r - 1))) =
      (caps.map fun c => (c.weight : ℝ) * (c.multiplicity : ℝ) * capWeight c r / 2) := by
    apply List.map_congr_left
    intro c hc
    rw [E1_smul, E1_rvP _ h.pr h.k7,
      capWeight_cell (List.all_eq_true.mp h.cut c hc) h.hr]
    push_cast; ring
  have ht : ((tents.map fun c => E1 (A1.smul (c.weight * c.capacity / 2) (rvP c.vector k)) (r - 1))) =
      (tents.map fun c => (c.weight : ℝ) * (c.capacity : ℝ) * radialValue c.vector r / 2) := by
    apply List.map_congr_left
    intro c _
    rw [E1_smul, E1_rvP _ h.pr h.k7]
    push_cast; ring
  have ha : ((allocations.map fun c => E1 (A1.smul (c.weight / 2) (rvP c.vector k)) (r - 1))) =
      (allocations.map fun c => (c.weight : ℝ) * radialValue c.vector r / 2) := by
    apply List.map_congr_left
    intro c _
    rw [E1_smul, E1_rvP _ h.pr h.k7]
    push_cast; ring
  have hs : (sphericalRays.map fun c => (c.weight : ℝ) * (c.bound : ℝ) * indicator c.radius r / 2) =
      (sphericalRays.map fun c => (c.weight : ℝ) * (c.bound : ℝ) * (indQ k c.radius : ℝ) / 2) := by
    apply List.map_congr_left
    intro c hc
    have hR : c.radius ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl (Or.inl ⟨c, hc, rfl⟩))
    rw [ind_of_mem h.ok h.hr hR]
  have hd : (conditionalRays.map fun c => 23 * (c.weight : ℝ) *
      (indicator c.outer r - indicator c.inner r) / 2) =
      (conditionalRays.map fun c => 23 * (c.weight : ℝ) *
      ((indQ k c.outer : ℝ) - (indQ k c.inner : ℝ)) / 2) := by
    apply List.map_congr_left
    intro c hc
    have hi : c.inner ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact Or.inr (Or.inl (Or.inr ⟨c, hc, by simp⟩))
    have ho : c.outer ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact Or.inr (Or.inl (Or.inr ⟨c, hc, by simp⟩))
    rw [ind_of_mem h.ok h.hr hi, ind_of_mem h.ok h.hr ho]
  have hn : (countPolynomials.map fun c => countLinear c r) =
      (countPolynomials.map fun c => (c.weight : ℝ) * ((List.range c.radii.length).map fun i =>
        ((c.linear.getD i 0 : ℚ) : ℝ) * (indQ k (c.radii.getD i 0) : ℝ)).sum) := by
    apply List.map_congr_left
    intro c hc
    unfold countLinear
    congr 2
    apply List.map_congr_left
    intro i hi
    have hR : c.radii.getD i 0 ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
      exact Or.inr (Or.inr ⟨c, hc, i, hi, rfl⟩)
    rw [ind_of_mem h.ok h.hr hR]
  rw [hc, ht, ha, hs, hd, hn]
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat, cast_sum_map]
  ring

/-- Self-cap decision on a cell: `L(r) = r² + d² - a² - 2 d σ r ≤ 0` throughout. -/
def selfLP (c : Cap) : P1 := [1 + c.d ^ 2 - c.a2 - 2 * c.d * c.sigma, 2 - 2 * c.d * c.sigma, 1]

def selfOn (k : ℕ) (c : Cap) : Bool :=
  decide (0 ≤ low1 ((cellHi k - cellLo k) / 2)
    (pshift qAlg ((cellLo k + cellHi k) / 2 - 1) (A1.smul (-1) (selfLP c))))

def selfP (k : ℕ) : P1 :=
  psum qAlg (caps.map fun c =>
    A1.smul (c.weight * capCut k c * (if selfOn k c then 1 else 0)) (rvP c.vector k))

theorem E1_selfLP (c : Cap) (r : ℝ) :
    E1 (selfLP c) (r - 1) = r * r + (c.d : ℝ) ^ 2 - c.a2 - 2 * c.d * c.sigma * r := by
  simp [selfLP, E1]; ring

theorem in_cell_box {k : ℕ} {r : ℝ} (hr : InCell k r) :
    |(r - 1) - (((cellLo k + cellHi k) / 2 - 1 : ℚ) : ℝ)| ≤ (((cellHi k - cellLo k) / 2 : ℚ) : ℝ) := by
  obtain ⟨h1, h2, _⟩ := hr
  push_cast
  rw [abs_le]; constructor <;> linarith

theorem selfOn_sound {k : ℕ} {c : Cap} (hs : selfOn k c = true) {r : ℝ} (hr : InCell k r) :
    r * r + (c.d : ℝ) ^ 2 - c.a2 - 2 * c.d * c.sigma * r ≤ 0 := by
  unfold selfOn at hs
  have h0 := decide_eq_true_eq.mp hs
  have h0' : (0 : ℝ) ≤ ((low1 ((cellHi k - cellLo k) / 2)
      (pshift qAlg ((cellLo k + cellHi k) / 2 - 1) (A1.smul (-1) (selfLP c))) : ℚ) : ℝ) := by
    exact_mod_cast h0
  have := low1_shift_sound (in_cell_box hr) (A1.smul (-1) (selfLP c))
  rw [E1_smul, E1_selfLP] at this
  push_cast at this
  linarith

/-- The cell is inside `[1, 7/4]`. -/
theorem cell_range {k : ℕ} {r : ℝ} (hr : InCell k r) (hk : k < 7) : 1 ≤ r ∧ r ≤ 7 / 4 := by
  obtain ⟨h1, h2, _⟩ := hr
  interval_cases k <;> simp [cellLo, cellHi, breaks] at h1 h2 <;> constructor <;> linarith

theorem selfP_le {k : ℕ} {r : ℝ} (h : CellOne k r) :
    E1 (selfP k) (r - 1) ≤ capsCorrection r r 1 := by
  have hr := cell_range h.hr h.k7
  unfold selfP capsCorrection
  rw [E1_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  have hv := caps_data_valid c hc
  simp only [Function.comp, E1_smul, E1_rvP _ h.pr h.k7]
  rw [capWeight_cell (List.all_eq_true.mp h.cut c hc) h.hr]
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hv.2.2.2.2.1
  have hrv : 0 ≤ radialValue c.vector r := radialValue_nonneg _ hv.2.2.2.2.2.1 hr.1 hr.2
  have hcut : (0 : ℝ) ≤ (capCut k c : ℝ) := by
    unfold capCut
    cases c.cutoff with
    | none => norm_num
    | some C => simp only; split_ifs <;> norm_num
  have hP := capProbability_nonneg c r 1
  by_cases hs : selfOn k c = true
  · have hL := selfOn_sound hs h.hr
    have hP1 : capProbability c r 1 = 1 := by
      have hd : (0 : ℝ) < c.d := by exact_mod_cast hv.1
      have hr0 : 0 < r := by linarith [hr.1]
      have h2 : 0 < 2 * (c.d : ℝ) * r := by positivity
      have hA : (r * r + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * r) - c.sigma * 1 ≤ 0 := by
        have : (r * r + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * r) ≤ c.sigma * 1 := by
          rw [div_le_iff₀ h2]; nlinarith
        linarith
      unfold capProbability
      dsimp only
      rw [if_pos (by ring), if_pos hA]
    rw [hP1, if_pos hs]
    apply le_of_eq
    push_cast; ring
  · rw [if_neg hs]
    have : 0 ≤ (c.weight : ℝ) * ((capCut k c : ℝ) * radialValue c.vector r * capProbability c r 1 +
        (capCut k c : ℝ) * radialValue c.vector r * capProbability c r 1) / 2 := by
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg hw
      have := mul_nonneg (mul_nonneg hcut hrv) hP
      linarith
    calc _ = (0 : ℝ) := by push_cast; ring
      _ ≤ _ := this

/-- Polynomial upper bound of the ungauged diagonal source on cell `k`. -/
def Upoly (ghat : P1) (k : ℕ) : P1 :=
  A1.add ghat (A1.add (A1.smul 2 (linP k)) (A1.add (diag3 (coreP k k)) (A1.smul (-1) (selfP k))))

def ScalarUpper (ghat : P1) : Prop :=
  ∀ r : ℝ, 1 ≤ r → r ≤ 102597 / 100000 → scalarRadius r ≤ E1 ghat (r - 1)

theorem ungauged_le {ghat : P1} (hg : ScalarUpper ghat) {k : ℕ} {r : ℝ} (h : CellOne k r)
    (hk5 : k < 5) : ungaugedPair r ≤ E1 (Upoly ghat k) (r - 1) := by
  have hr := cell_range h.hr h.k7
  have hr5 : r ≤ 102597 / 100000 := by
    have := h.hr.2.1
    interval_cases k <;> simp [cellHi, breaks] at this <;> linarith
  have hcp : CellPair k k r r := ⟨h.hr, h.hr, h.pr, h.pr, h.k7, h.k7, h.ok, h.ok⟩
  have hcore : E1 (diag3 (coreP k k)) (r - 1) = corePair r r 1 := by
    rw [E1_diag3]
    have := E3_coreP hcp 1
    exact this
  have ht := tentsCorrection_nonneg hr.1 hr.1 hr.2 hr.2 1
  have ha := allocationsCorrection_nonneg hr.1 hr.1 hr.2 hr.2 1
  have hgr := graphsCorrection_nonneg r r 1
  have hs := selfP_le h
  have hsc := hg r hr.1 hr5
  have e : ungaugedPair r = scalarRadius r + 2 * rawLinear r +
      (corePair r r 1 - capsCorrection r r 1 - tentsCorrection r r 1 -
        allocationsCorrection r r 1 - graphsCorrection r r 1) := by
    unfold ungaugedPair rawPair corePair; ring
  unfold Upoly
  simp only [E1_add, E1_smul, hcore, E1_linP h]
  rw [e]
  push_cast
  linarith

/-! ## Gauge and base polynomial -/

def psiQ (k : ℕ) : ℚ := indQ k gaugeRadius / gaugeCount

theorem gaugePsi_cell {k : ℕ} (hok : cellOK k = true) {r : ℝ} (hr : InCell k r) :
    gaugePsi r = (psiQ k : ℝ) := by
  have hR : gaugeRadius ∈ allRadii := by simp [allRadii]
  unfold gaugePsi psiQ
  rw [ind_of_mem hok hr hR]
  push_cast; rfl

theorem psiQ_range (k : ℕ) : 0 ≤ psiQ k ∧ psiQ k < 1 := by
  unfold psiQ indQ gaugeCount
  split_ifs <;> norm_num

def gaugeP (ghat : P1) (kr ks : ℕ) : P3 :=
  A3.add (A3.smul (-(psiQ ks / (1 - psiQ kr)) / 2) (liftU (Upoly ghat kr)))
    (A3.smul (-(psiQ kr / (1 - psiQ ks)) / 2) (liftV (Upoly ghat ks)))

def lamP (lam : ℚ) : P3 := liftT [0, 0, lam * (133 / 250) ^ 2, 0, -lam]

def baseP (ghat : P1) (lam : ℚ) (kr ks : ℕ) : P3 :=
  A3.add (A3.smul (-1) (coreP kr ks)) (A3.add (gaugeP ghat kr ks) (lamP lam))

/-- The base polynomial bounds the smooth part of `-pair - λ q` from below. -/
theorem baseP_le {ghat : P1} (hg : ScalarUpper ghat) (lam : ℚ) {kr ks : ℕ} {r s : ℝ}
    (h : CellPair kr ks r s) (hr5 : kr < 5) (hs5 : ks < 5)
    (hcr : capsCutOK kr = true) (hcs : capsCutOK ks = true) (t : ℝ) :
    E3 (baseP ghat lam kr ks) (r - 1) (s - 1) t ≤
      -corePair r s t +
        (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 -
        lam * (t ^ 4 - (133 / 250) ^ 2 * t ^ 2) := by
  have hUr := ungauged_le hg ⟨h.hr, h.pr, h.kr7, h.okr, hcr⟩ hr5
  have hUs := ungauged_le hg ⟨h.hs, h.ps, h.ks7, h.oks, hcs⟩ hs5
  have hpr := gaugePsi_cell h.okr h.hr
  have hps := gaugePsi_cell h.oks h.hs
  obtain ⟨hr0, hr1⟩ := psiQ_range kr
  obtain ⟨hs0, hs1⟩ := psiQ_range ks
  have hr0' : (0 : ℝ) ≤ psiQ kr := by exact_mod_cast hr0
  have hs0' : (0 : ℝ) ≤ psiQ ks := by exact_mod_cast hs0
  have hr1' : (0 : ℝ) < 1 - psiQ kr := by
    have : (psiQ kr : ℝ) < 1 := by exact_mod_cast hr1
    linarith
  have hs1' : (0 : ℝ) < 1 - psiQ ks := by
    have : (psiQ ks : ℝ) < 1 := by exact_mod_cast hs1
    linarith
  have key : E3 (baseP ghat lam kr ks) (r - 1) (s - 1) t =
      -corePair r s t -
      ((psiQ ks : ℝ) / (1 - psiQ kr)) / 2 * E1 (Upoly ghat kr) (r - 1) -
      ((psiQ kr : ℝ) / (1 - psiQ ks)) / 2 * E1 (Upoly ghat ks) (s - 1) -
      lam * (t ^ 4 - (133 / 250) ^ 2 * t ^ 2) := by
    unfold baseP gaugeP lamP
    simp only [E3_add, E3_smul, E3_liftU, E3_liftV, E3_liftT, E3_coreP h]
    simp only [E1, peval_cons, peval_nil]
    push_cast; ring
  rw [key]
  unfold gaugeWeight
  rw [hpr, hps]
  have c1 : (0 : ℝ) ≤ (psiQ ks : ℝ) / (1 - psiQ kr) := div_nonneg hs0' hr1'.le
  have c2 : (0 : ℝ) ≤ (psiQ kr : ℝ) / (1 - psiQ ks) := div_nonneg hr0' hs1'.le
  have k1 := mul_le_mul_of_nonneg_left hUr c1
  have k2 := mul_le_mul_of_nonneg_left hUs c2
  have e1 : -ungaugedPair r / (1 - (psiQ kr : ℝ)) * psiQ ks =
      -((psiQ ks : ℝ) / (1 - psiQ kr) * ungaugedPair r) := by ring
  have e2 : -ungaugedPair s / (1 - (psiQ ks : ℝ)) * psiQ kr =
      -((psiQ kr : ℝ) / (1 - psiQ ks) * ungaugedPair s) := by ring
  rw [e1, e2]
  linarith

end D4Bound.KBN
