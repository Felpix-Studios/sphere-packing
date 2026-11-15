import D4Bound.KernelBoxNativeNode
import D4Bound.KernelBoxNativeScalar
import D4Bound.V7PairSign
import D4Bound.V7CyclicCases

/-!
# The 28 exterior cyclic cases by the native kernel-box method

When one side `d` of the triangle exceeds `7/4`, the cyclic sum reduces to the single pair
term `pair r s (sideCos r s d)`. This module proves `pair r s t ≤ 0` on every radial cell
pair `(k_r, k_s)`, `k_r ≤ k_s < 7`, for all `t` with `2 r s t < r² + s² - 49/16`, reusing the
lower-polynomial machinery of `KernelBoxNativeNode`. Differences: all seven radial pieces;
cap cut-offs are decided on each box (cut-off `707107/500000` lies inside piece 5); the gauge
uses `Upoly` on pieces 0-4 and `gaugeWeight ≥ 0` (from `ungaugedPair_nonpos`) on pieces 5-6;
boxes outside the exterior region are discarded by a polynomial sign test.
`outside_of_check` delivers the `outside` hypothesis of `V7.cyclicSign_of_112_cases`.
-/

namespace D4Bound.KBN
open V7

/-- Radial facts about one variable (no cap cut-off decision). -/
structure RadOne (k : ℕ) (y : ℝ) : Prop where
  hr : InCell k y
  pr : radialPiece y = k
  k7 : k < 7

/-- Cut-off factor decided on the box coordinate range `[1 + cc - h, 1 + cc + h]`. -/
def cutLo (c : Cap) (cc h : ℚ) : ℚ :=
  match c.cutoff with
  | none => 1
  | some C => if C < 1 + cc - h then 1 else 0

theorem cutLo_nonneg (c : Cap) (cc h : ℚ) : 0 ≤ cutLo c cc h := by
  unfold cutLo
  cases c.cutoff with
  | none => norm_num
  | some C => simp only; split_ifs <;> norm_num

theorem capWeight_ge_cut {c : Cap} (hv : CapValid c) {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 7 / 4)
    {cc h : ℚ} (hb : |(y - 1) - cc| ≤ h) :
    (cutLo c cc h : ℝ) * radialValue c.vector y ≤ capWeight c y := by
  have hcw := capWeight_nonneg hv hy1 hy2
  cases hC : c.cutoff with
  | none => simp [cutLo, capWeight, hC]
  | some C =>
    by_cases h1 : C < 1 + cc - h
    · have hb' := abs_box hb
      have h1' : ((C : ℚ) : ℝ) < ((1 + cc - h : ℚ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      have : (C : ℝ) < y := by linarith
      simp [cutLo, capWeight, hC, h1, this]
    · simp only [cutLo, hC, h1, if_false, Rat.cast_zero, zero_mul]
      exact hcw

def capTermX (ky : ℕ) (b : Box) (c : Cap) (sd : Bool) : P3 :=
  if decide (1 / 10 ^ 13 ≤ c.weight) then
    A3.smul (c.weight / 2 * cutLo c (if sd then b.cu else b.cv) (if sd then b.hu else b.hv) *
      capLevel b c sd) (liftX (!sd) (rvP c.vector ky))
  else A3.zero

def capsLowX (kr ks : ℕ) (b : Box) : P3 :=
  psum A2 (caps.map fun c => A3.add (capTermX ks b c false) (capTermX kr b c true))

theorem capTermX_core {ky : ℕ} {b : Box} {r s t x y : ℝ} {c : Cap} (hc : c ∈ caps)
    (sd : Bool) (hx : XSel sd r s t x) (hy : XSel (!sd) r s t y) (hyc : RadOne ky y)
    (hyb : |(y - 1) - ((if sd then b.cu else b.cv) : ℚ)| ≤ ((if sd then b.hu else b.hv) : ℚ))
    (hx0 : 0 < x) (hm : b.Mem (r - 1) (s - 1) t) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    E3 (capTermX ky b c sd) (r - 1) (s - 1) t ≤
      (c.weight : ℝ) * capWeight c y * capProbability c x t / 2 := by
  have hv := caps_data_valid c hc
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hv.2.2.2.2.1
  have hyr := cell_range hyc.hr hyc.k7
  have hcw := capWeight_nonneg hv hyr.1 hyr.2
  have hP := capProbability_nonneg c x t
  have hrv := radialValue_nonneg _ hv.2.2.2.2.2.1 hyr.1 hyr.2
  unfold capTermX
  by_cases hsel : decide (1 / 10 ^ 13 ≤ c.weight) = true
  · rw [if_pos hsel]
    obtain ⟨hl0, hlev⟩ := capLevel_sound hv hx hx0 hm ht1 ht2 (b := b)
    rw [E3_smul, hy, E1_rvP _ hyc.pr hyc.k7]
    have hcut := capWeight_ge_cut hv hyr.1 hyr.2 hyb
    have hc0 : (0 : ℝ) ≤ (cutLo c (if sd then b.cu else b.cv) (if sd then b.hu else b.hv) : ℝ) := by
      exact_mod_cast cutLo_nonneg _ _ _
    have hl0' : (0 : ℝ) ≤ (capLevel b c sd : ℝ) := by exact_mod_cast hl0
    have k1 := mul_le_mul_of_nonneg_left hcut (mul_nonneg hw hl0')
    have k2 := mul_le_mul_of_nonneg_left hlev (mul_nonneg hw hcw)
    push_cast
    nlinarith [k1, k2]
  · rw [if_neg hsel, E3_zero]
    have := mul_nonneg (mul_nonneg hw hcw) hP
    linarith

/-- Hypotheses at a node of the exterior search. -/
structure XHyp (kr ks : ℕ) (b : Box) (r s t : ℝ) : Prop where
  cp : CellPair kr ks r s
  mem : b.Mem (r - 1) (s - 1) t
  t1 : -1 ≤ t
  t2 : t ≤ 1

theorem XHyp.range_r {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : XHyp kr ks b r s t) :
    1 ≤ r ∧ r ≤ 7 / 4 := cell_range h.cp.hr h.cp.kr7
theorem XHyp.range_s {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : XHyp kr ks b r s t) :
    1 ≤ s ∧ s ≤ 7 / 4 := cell_range h.cp.hs h.cp.ks7

theorem capsLowX_le {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : XHyp kr ks b r s t) :
    E3 (capsLowX kr ks b) (r - 1) (s - 1) t ≤ capsCorrection r s t := by
  unfold capsLowX capsCorrection
  rw [E3_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  have h0 := capTermX_core (ky := ks) hc false (xsel_false r s t) (xsel_true r s t)
    ⟨h.cp.hs, h.cp.ps, h.cp.ks7⟩ (by simpa using h.mem.2.1) (by linarith [h.range_r.1])
    h.mem h.t1 h.t2
  have h1 := capTermX_core (ky := kr) hc true (xsel_true r s t) (xsel_false r s t)
    ⟨h.cp.hr, h.cp.pr, h.cp.kr7⟩ (by simpa using h.mem.1) (by linarith [h.range_s.1])
    h.mem h.t1 h.t2
  simp only [Function.comp, E3_add]
  linarith

theorem tentTerm_coreX {ky : ℕ} {b : Box} {r s t x y : ℝ} {c : Tent} (hc : c ∈ tents)
    (sd : Bool) (hx : XSel sd r s t x) (hy : XSel (!sd) r s t y) (hyc : RadOne ky y) :
    E3 (tentTerm ky b c sd) (r - 1) (s - 1) t ≤
      (c.weight : ℝ) * radialValue c.vector y * tentProfile c.d x t / 2 := by
  obtain ⟨hw0, hvv, _⟩ := tent_data_ok c hc
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hw0
  have hyr := cell_range hyc.hr hyc.k7
  have hrv := radialValue_nonneg _ hvv hyr.1 hyr.2
  have hT : 0 ≤ tentProfile c.d x t := le_max_left _ _
  unfold tentTerm
  by_cases hsel : 0 < centre b (tentP c.d sd)
  · rw [if_pos hsel, E3_smul, E3_mul, hy, E3_tentP hx, E1_rvP _ hyc.pr hyc.k7]
    have hle : 1 - 2 * (x * x + (c.d : ℝ) * c.d + 2 * c.d * x * t) ≤ tentProfile c.d x t :=
      le_max_right _ _
    have := mul_le_mul_of_nonneg_left hle (mul_nonneg hw hrv)
    push_cast
    nlinarith [this]
  · rw [if_neg hsel, E3_zero]
    have := mul_nonneg (mul_nonneg hw hrv) hT
    linarith

theorem tentsLow_leX {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : XHyp kr ks b r s t) :
    E3 (tentsLow kr ks b) (r - 1) (s - 1) t ≤ tentsCorrection r s t := by
  unfold tentsLow tentsCorrection
  rw [E3_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  have h0 := tentTerm_coreX (ky := ks) (b := b) hc false (xsel_false r s t) (xsel_true r s t)
    ⟨h.cp.hs, h.cp.ps, h.cp.ks7⟩
  have h1 := tentTerm_coreX (ky := kr) (b := b) hc true (xsel_true r s t) (xsel_false r s t)
    ⟨h.cp.hr, h.cp.pr, h.cp.kr7⟩
  simp only [Function.comp, E3_add]
  linarith

theorem allocTerm_leX {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : XHyp kr ks b r s t)
    {c : AllocationData} (hc : c ∈ allocations) :
    E3 (allocTerm kr ks b c) (r - 1) (s - 1) t ≤
      (c.weight : ℝ) * (radialValue c.vector r + radialValue c.vector s) *
        allocationProfile c (r * r + s * s + 2 * r * s * t) / 2 := by
  obtain ⟨hw0, hvv, _⟩ := allocation_data_ok c hc
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hw0
  have hry := h.range_r
  have hsy := h.range_s
  have hR : 0 ≤ radialValue c.vector r + radialValue c.vector s :=
    add_nonneg (radialValue_nonneg _ hvv hry.1 hry.2) (radialValue_nonneg _ hvv hsy.1 hsy.2)
  have hprof := allocationProfile_nonneg c (r * r + s * s + 2 * r * s * t)
  have hRe : E3 (allocR kr ks c) (r - 1) (s - 1) t = radialValue c.vector r + radialValue c.vector s := by
    simp only [allocR, E3_add, E3_liftU, E3_liftV, E1_rvP _ h.cp.pr h.cp.kr7, E1_rvP _ h.cp.ps h.cp.ks7]
  have hq0 : 0 ≤ r * r + s * s + 2 * r * s * t := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (by linarith : (0 : ℝ) ≤ s),
      sq_nonneg (r - s), h.t1]
  have hbase : 0 ≤ (c.weight : ℝ) * (radialValue c.vector r + radialValue c.vector s) *
      allocationProfile c (r * r + s * s + 2 * r * s * t) / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hw hR) hprof) (by norm_num)
  unfold allocTerm
  by_cases h2 : c.twoLevel = true
  · rw [if_pos h2]
    by_cases hin : pos b (A3.add (const3 (c.inner ^ 2)) (A3.smul (-1) qP)) = true
    · rw [if_pos hin, E3_smul, hRe]
      have hlt := pos_sound hin h.mem
      rw [E3_add, E3_const3, E3_smul, E3_qP] at hlt
      have hp1 : allocationProfile c (r * r + s * s + 2 * r * s * t) = 1 := by
        unfold allocationProfile
        rw [if_pos h2, if_pos (by push_cast at hlt; linarith)]
      rw [hp1]; push_cast; apply le_of_eq; ring
    · rw [if_neg hin]
      by_cases hout : nonneg b (A3.add (const3 (c.outer ^ 2)) (A3.smul (-1) qP)) = true
      · rw [if_pos hout, E3_smul, hRe]
        have hle := nonneg_sound hout h.mem
        rw [E3_add, E3_const3, E3_smul, E3_qP] at hle
        have hp : 1 / 2 ≤ allocationProfile c (r * r + s * s + 2 * r * s * t) := by
          unfold allocationProfile
          rw [if_pos h2]
          split_ifs
          · norm_num
          · norm_num
          · push_cast at hle; linarith
        have := mul_le_mul_of_nonneg_left hp (mul_nonneg hw hR)
        push_cast
        nlinarith [this]
      · rw [if_neg hout, E3_zero]; exact hbase
  · rw [if_neg h2]
    by_cases hcen : 0 < centre b oneMinus2q
    · rw [if_pos hcen, E3_smul, E3_mul, hRe]
      have hcl := profile_classical (by simpa using h2) hq0
      have he : E3 oneMinus2q (r - 1) (s - 1) t = 1 - 2 * (r * r + s * s + 2 * r * s * t) := by
        simp only [oneMinus2q, E3_add, E3_const3, E3_smul, E3_qP]; push_cast; ring
      rw [he]
      have := mul_le_mul_of_nonneg_left hcl (mul_nonneg hw hR)
      push_cast
      nlinarith [this]
    · rw [if_neg hcen, E3_zero]; exact hbase

theorem allocsLow_leX {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : XHyp kr ks b r s t) :
    E3 (allocsLow kr ks b) (r - 1) (s - 1) t ≤ allocationsCorrection r s t := by
  unfold allocsLow allocationsCorrection
  rw [E3_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  simp only [Function.comp]
  exact allocTerm_leX h hc

/-! ## Gauge on all seven pieces -/

def gH (ghat : P1) (k k' : ℕ) : P1 :=
  if k < 5 then A1.smul (-(psiQ k' / (1 - psiQ k)) / 2) (Upoly ghat k) else []

theorem gH_le {ghat : P1} (hg : ScalarUpper ghat) {k k' : ℕ} {r s : ℝ} (hr : InCell k r)
    (pr : radialPiece r = k) (k7 : k < 7) (okr : cellOK k = true) (hs : InCell k' s)
    (oks : cellOK k' = true) (hcut : k < 5 → capsCutOK k = true) :
    E1 (gH ghat k k') (r - 1) ≤ gaugeWeight r * gaugePsi s / 2 := by
  have hpr := gaugePsi_cell okr hr
  have hps := gaugePsi_cell oks hs
  obtain ⟨hr0, hr1⟩ := psiQ_range k
  obtain ⟨hs0, hs1⟩ := psiQ_range k'
  have hr0' : (0 : ℝ) ≤ psiQ k := by exact_mod_cast hr0
  have hs0' : (0 : ℝ) ≤ psiQ k' := by exact_mod_cast hs0
  have hr1' : (0 : ℝ) < 1 - psiQ k := by
    have : (psiQ k : ℝ) < 1 := by exact_mod_cast hr1
    linarith
  unfold gaugeWeight
  rw [hpr, hps]
  unfold gH
  by_cases hk : k < 5
  · rw [if_pos hk, E1_smul]
    have hU := ungauged_le hg ⟨hr, pr, k7, okr, hcut hk⟩ hk
    have c1 : (0 : ℝ) ≤ (psiQ k' : ℝ) / (1 - psiQ k) := div_nonneg hs0' hr1'.le
    have k1 := mul_le_mul_of_nonneg_left hU c1
    have e1 : -ungaugedPair r / (1 - (psiQ k : ℝ)) * psiQ k' / 2 =
        -((psiQ k' : ℝ) / (1 - psiQ k) * ungaugedPair r) / 2 := by ring
    rw [e1]
    push_cast
    linarith
  · rw [if_neg hk]
    have hrr := cell_range hr k7
    have hn := ungaugedPair_nonpos hrr.1 hrr.2
    have : 0 ≤ -ungaugedPair r / (1 - (psiQ k : ℝ)) * psiQ k' / 2 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (div_nonneg (by linarith) hr1'.le) hs0'
    simpa [E1] using this

def baseX (ghat : P1) (kr ks : ℕ) : P3 :=
  A3.add (A3.smul (-1) (coreP kr ks)) (A3.add (liftU (gH ghat kr ks)) (liftV (gH ghat ks kr)))

theorem baseX_ok {ghat : P1} (hg : ScalarUpper ghat) {kr ks : ℕ}
    (hcr : kr < 5 → capsCutOK kr = true) (hcs : ks < 5 → capsCutOK ks = true) :
    BaseOK (baseX ghat kr ks) 0 kr ks := by
  intro r s t h
  have h1 := gH_le hg h.hr h.pr h.kr7 h.okr h.hs h.oks hcr
  have h2 := gH_le hg h.hs h.ps h.ks7 h.oks h.hr h.okr hcs
  unfold baseX
  simp only [E3_add, E3_smul, E3_liftU, E3_liftV, E3_coreP h]
  push_cast
  linarith

/-- Base condition with `λ = 0`, for `t ∈ [-1, 1]`. -/
def BaseOKt (B : P3) (kr ks : ℕ) : Prop :=
  ∀ r s t : ℝ, CellPair kr ks r s → -1 ≤ t → t ≤ 1 →
    E3 B (r - 1) (s - 1) t ≤ -corePair r s t +
      (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2

theorem BaseOKt_of {B : P3} {kr ks : ℕ} (h : BaseOK B 0 kr ks) : BaseOKt B kr ks := by
  intro r s t hc _ _
  have := h r s t hc
  push_cast at this
  linarith

/-- Dyadic rounding (any rounding is sound: the exact error is bounded below). -/
def roundQ (N : ℕ) (q : ℚ) : ℚ := ((q * 2 ^ N).floor : ℚ) / 2 ^ N
def roundP3 (N : ℕ) (p : P3) : P3 := p.map fun a => a.map fun b => b.map (roundQ N)
def errP3 (N : ℕ) (p : P3) : ℚ := absP (abs2 1 1) 1 (A3.add p (A3.smul (-1) (roundP3 N p)))
def baseR (N : ℕ) (p : P3) : P3 := A3.add (roundP3 N p) (const3 (-(errP3 N p)))

theorem baseR_ok {B : P3} {kr ks : ℕ} (N : ℕ) (h : BaseOKt B kr ks) :
    BaseOKt (baseR N B) kr ks := by
  intro r s t hc ht1 ht2
  have h0 := h r s t hc ht1 ht2
  have hr := cell_range hc.hr hc.kr7
  have hs := cell_range hc.hs hc.ks7
  have hu : |r - 1| ≤ ((1 : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith
  have hv : |s - 1| ≤ ((1 : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith
  have htt : |t| ≤ ((1 : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith
  have hD := absP_sound (ev := fun c => E2 c (s - 1) t) (fun a => (bounds2 hv htt a).2) hu
    (A3.add B (A3.smul (-1) (roundP3 N B)))
  have hD' : |E3 (A3.add B (A3.smul (-1) (roundP3 N B))) (r - 1) (s - 1) t| ≤
      (errP3 N B : ℝ) := hD
  rw [E3_add, E3_smul] at hD'
  have := neg_abs_le (E3 B (r - 1) (s - 1) t + ((-1 : ℚ) : ℝ) * E3 (roundP3 N B) (r - 1) (s - 1) t)
  unfold baseR
  rw [E3_add, E3_const3]
  push_cast at hD' this ⊢
  linarith

/-! ## The exterior node polynomial and search -/

def nodeX (B : P3) (kr ks : ℕ) (b : Box) : P3 :=
  A3.add B (A3.add (capsLowX kr ks b) (A3.add (tentsLow kr ks b)
    (A3.add (allocsLow kr ks b) (const3 (graphLow b)))))

theorem nodeX_le {B : P3} {kr ks : ℕ} (hB : BaseOKt B kr ks) {b : Box}
    {r s t : ℝ} (h : XHyp kr ks b r s t) :
    E3 (nodeX B kr ks b) (r - 1) (s - 1) t ≤ -pair r s t := by
  have h0 := hB r s t h.cp h.t1 h.t2
  have hc := capsLowX_le h
  have ht := tentsLow_leX h
  have ha := allocsLow_leX h
  have hg := graphLow_le (r := r) (s := s) (t := t) h.mem
  have e : -pair r s t = -corePair r s t + capsCorrection r s t +
      tentsCorrection r s t + allocationsCorrection r s t + graphsCorrection r s t +
      (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 := by
    unfold pair rawPair corePair; ring
  unfold nodeX
  simp only [E3_add, E3_const3]
  rw [e]
  linarith

/-- `2 r s t - r² - s² + 49/16`; positive exactly outside the exterior region. -/
def extP : P3 :=
  A3.add (A3.smul 2 (A3.mul (A3.mul (liftU [1, 1]) (liftV [1, 1])) (liftT [0, 1])))
    (A3.add (A3.smul (-1) (liftU [1, 2, 1])) (A3.add (A3.smul (-1) (liftV [1, 2, 1]))
      (const3 (49 / 16))))

theorem E3_extP (r s t : ℝ) :
    E3 extP (r - 1) (s - 1) t = 2 * r * s * t - r * r - s * s + 49 / 16 := by
  simp only [extP, E3_add, E3_smul, E3_mul, E3_const3, E3_liftU, E3_liftV, E3_liftT,
    E1_quad, E1_lin, E1_T]
  push_cast; ring

/-- Multiplier for the exterior constraint, matched to the `t`-slope at the centre. -/
def muOf (S G : P3) : ℚ :=
  if 0 < coef G 0 0 1 then max 0 (-(coef S 0 0 1) / coef G 0 0 1) else 0

theorem muOf_nonneg (S G : P3) : 0 ≤ muOf S G := by
  unfold muOf; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

def searchX (B : P3) (kr ks : ℕ) : ℕ → Box → Bool
  | 0, b => pos b extP || decide (0 ≤ lowOn b (nodeX B kr ks b))
  | n + 1, b =>
    if pos b extP then true
    else
      let S := shift3 b.cu b.cv b.ct (nodeX B kr ks b)
      if 0 ≤ low3 b.hu b.hv b.ht S then true
      else
        let G := shift3 b.cu b.cv b.ct extP
        if 0 ≤ low3 b.hu b.hv b.ht (A3.add S (A3.smul (muOf S G) G)) then true
        else
          let bs := splitBox b (chooseAxis b S)
          searchX B kr ks n bs.1 && searchX B kr ks n bs.2

theorem shift_eval {b : Box} (P : P3) (r s t : ℝ) :
    E3 (shift3 b.cu b.cv b.ct P) (r - 1 - b.cu) (s - 1 - b.cv) (t - b.ct) =
      E3 P (r - 1) (s - 1) t := by
  rw [E3_shift3]; simp only [add_sub_cancel]

def TargetX (r s t : ℝ) : Prop := 2 * r * s * t < r * r + s * s - 49 / 16 → 0 ≤ -pair r s t

theorem searchX_sound {B : P3} {kr ks : ℕ} (hB : BaseOKt B kr ks) :
    ∀ (n : ℕ) (b : Box), searchX B kr ks n b = true →
      ∀ r s t : ℝ, XHyp kr ks b r s t → TargetX r s t
  | 0, b, hs, r, s, t, h => by
    intro hreg
    simp only [searchX, Bool.or_eq_true, decide_eq_true_eq] at hs
    rcases hs with hp | hl
    · have := pos_sound hp h.mem
      rw [E3_extP] at this; linarith
    · have h0 : (0 : ℝ) ≤ (lowOn b (nodeX B kr ks b) : ℝ) := by exact_mod_cast hl
      have := lowOn_sound h.mem (nodeX B kr ks b)
      have := nodeX_le hB h
      linarith
  | n + 1, b, hs, r, s, t, h => by
    intro hreg
    simp only [searchX] at hs
    split_ifs at hs with hp hlow hmu
    · have := pos_sound hp h.mem
      rw [E3_extP] at this; linarith
    · have h0 : (0 : ℝ) ≤ (lowOn b (nodeX B kr ks b) : ℝ) := by exact_mod_cast hlow
      have := lowOn_sound h.mem (nodeX B kr ks b)
      have := nodeX_le hB h
      linarith
    · set S := shift3 b.cu b.cv b.ct (nodeX B kr ks b)
      set G := shift3 b.cu b.cv b.ct extP
      have h0 : (0 : ℝ) ≤ (low3 b.hu b.hv b.ht (A3.add S (A3.smul (muOf S G) G)) : ℝ) := by
        exact_mod_cast hmu
      have hl := low3_sound h.mem.1 h.mem.2.1 h.mem.2.2 (A3.add S (A3.smul (muOf S G) G))
      rw [E3_add, E3_smul, shift_eval, shift_eval, E3_extP] at hl
      have hm0 : (0 : ℝ) ≤ (muOf S G : ℝ) := by exact_mod_cast muOf_nonneg S G
      have hneg : 2 * r * s * t - r * r - s * s + 49 / 16 < 0 := by linarith
      have := nodeX_le hB h
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hm0 hneg.le]
    · simp only [Bool.and_eq_true] at hs
      rcases splitBox_cover b (chooseAxis b (shift3 b.cu b.cv b.ct (nodeX B kr ks b))) h.mem
        with hm | hm
      · exact searchX_sound hB n _ hs.1 r s t { h with mem := hm } hreg
      · exact searchX_sound hB n _ hs.2 r s t { h with mem := hm } hreg

/-! ## Cells and the exterior obligation -/

def coverOK (lo hi c h : ℚ) : Bool := decide ((hi - lo) / 2 + |(lo + hi) / 2 - 1 - c| ≤ h)

theorem coverOK_sound {lo hi c h : ℚ} (hc : coverOK lo hi c h = true) {r : ℝ}
    (h1 : (lo : ℝ) ≤ r) (h2 : r ≤ hi) : |(r - 1) - c| ≤ h := by
  simp only [coverOK, decide_eq_true_eq] at hc
  have hc' : (((hi - lo) / 2 + |(lo + hi) / 2 - 1 - c| : ℚ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  have e1 : |(r - 1) - ((lo : ℝ) + hi) / 2 + 1| ≤ ((hi : ℝ) - lo) / 2 := by
    rw [abs_le]; constructor <;> linarith
  calc |(r - 1) - c| = |((r - 1) - ((lo : ℝ) + hi) / 2 + 1) + (((lo : ℝ) + hi) / 2 - 1 - c)| := by
        ring_nf
    _ ≤ |(r - 1) - ((lo : ℝ) + hi) / 2 + 1| + |((lo : ℝ) + hi) / 2 - 1 - c| := abs_add_le _ _
    _ ≤ h := by linarith

/-- Root box with dyadic centre; coverage of the cell is checked by `coverOK`. -/
def rootBoxX (kr ks : ℕ) : Box :=
  ⟨roundQ 30 ((cellLo kr + cellHi kr) / 2 - 1), roundQ 30 ((cellLo ks + cellHi ks) / 2 - 1), -1 / 4,
   roundQ 30 ((cellHi kr - cellLo kr) / 2) + 2 / 2 ^ 30,
   roundQ 30 ((cellHi ks - cellLo ks) / 2) + 2 / 2 ^ 30, 3 / 4⟩

def checkCellX (B : P3) (kr ks fuel : ℕ) : Bool :=
  cellOK kr && cellOK ks && decide (kr < 7) && decide (ks < 7) &&
    (decide (5 ≤ kr) || capsCutOK kr) && (decide (5 ≤ ks) || capsCutOK ks) &&
    coverOK (cellLo kr) (cellHi kr) (rootBoxX kr ks).cu (rootBoxX kr ks).hu &&
    coverOK (cellLo ks) (cellHi ks) (rootBoxX kr ks).cv (rootBoxX kr ks).hv &&
    searchX (baseR 100 B) kr ks fuel (rootBoxX kr ks)

def checkOutside (fuel : ℕ) : Bool :=
  (List.range 7).all fun kr => (List.range 7).all fun ks =>
    decide (ks < kr) || checkCellX (baseX ghat kr ks) kr ks fuel

theorem radialPiece_cell7 {k : ℕ} {r : ℝ} (hr : InCell k r) (hk : k < 7) :
    radialPiece r = k := by
  obtain ⟨h1, h2, h3⟩ := hr
  have hr74 : r ≤ 7 / 4 := by
    interval_cases k <;> simp [cellHi, breaks] at h2 <;> linarith
  rw [radialPiece_on_support hr74]
  interval_cases k <;> simp [cellLo, cellHi, breaks] at h1 h2 h3 <;>
    split_ifs <;> first | rfl | (exfalso; linarith)

theorem checkCellX_sound {ghat : P1} (hg : ScalarUpper ghat) {kr ks fuel : ℕ}
    (hc : checkCellX (baseX ghat kr ks) kr ks fuel = true) {r s t : ℝ}
    (hr : InCell kr r) (hs : InCell ks s) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) : TargetX r s t := by
  intro hreg
  simp only [checkCellX, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨okr, oks⟩, kr7⟩, ks7⟩, cr⟩, cs⟩, cvu⟩, cvv⟩, hsearch⟩ := hc
  have hB := baseR_ok 100 (BaseOKt_of (baseX_ok hg (kr := kr) (ks := ks)
    (fun h => cr.resolve_left (by omega)) (fun h => cs.resolve_left (by omega))))
  have cp : CellPair kr ks r s :=
    ⟨hr, hs, radialPiece_cell7 hr kr7, radialPiece_cell7 hs ks7, kr7, ks7, okr, oks⟩
  have hrr := cell_range hr kr7
  have hss := cell_range hs ks7
  have htu : t ≤ 1 / 2 := by
    by_contra hcon
    have h1 : r * r - r * s + s * s ≤ 49 / 16 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r - 1) (by linarith : (0:ℝ) ≤ 7/4 - r),
        mul_nonneg (by linarith : (0:ℝ) ≤ s - 1) (by linarith : (0:ℝ) ≤ 7/4 - s),
        mul_nonneg (by linarith : (0:ℝ) ≤ 7/4 - r) (by linarith : (0:ℝ) ≤ 7/4 - s)]
    have hrs : 0 < r * s := by nlinarith
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hcon) (by linarith : (0:ℝ) < 2 * r * s)
    nlinarith
  have hm : (rootBoxX kr ks).Mem (r - 1) (s - 1) t := by
    obtain ⟨a1, a2, _⟩ := hr
    obtain ⟨b1, b2, _⟩ := hs
    refine ⟨coverOK_sound cvu a1 a2, coverOK_sound cvv b1 b2, ?_⟩
    simp only [rootBoxX]; push_cast; rw [abs_le]; constructor <;> linarith
  exact searchX_sound hB fuel _ hsearch r s t ⟨cp, hm, ht1, ht2⟩ hreg

theorem inCell_of_regionOwns {k : ℕ} {r : ℝ} (h : RegionOwns k r) : InCell k r := by
  obtain ⟨hk, hl, hh⟩ := h
  have hlo : regionLo k = (cellLo k : ℝ) := by
    interval_cases k <;> simp [regionLo, cellLo, breaks]
  have hhi : regionHi k = (cellHi k : ℝ) := by
    interval_cases k <;> simp [regionHi, cellHi, breaks]
  rw [hlo] at hl
  rw [hhi] at hh
  refine ⟨?_, hh, ?_⟩
  · split_ifs at hl <;> linarith
  · intro hk0
    rw [if_neg (by omega)] at hl
    exact hl

/-- The `outside` hypothesis of `V7.cyclicSign_of_112_cases`, from two executable checks. -/
theorem outside_of_check {fuel : ℕ} (hs : scalarCheck = true) (hc : checkOutside fuel = true) :
    ∀ p ∈ outsideCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.val s →
      r ≤ s → 7 / 4 < d → d ≤ r + s → pair r s (sideCos r s d) ≤ 0 := by
  have hg := scalar_upper_of_check hs
  intro p hp r s d hr hs' hrs hd hdr
  have hle : p.1.val ≤ p.2.val := by
    simp only [outsideCases, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp
  have hcell := List.all_eq_true.mp (List.all_eq_true.mp hc p.1.val
    (List.mem_range.mpr p.1.isLt)) p.2.val (List.mem_range.mpr p.2.isLt)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hcell
  have hcx := hcell.resolve_left (by omega)
  have hrc := inCell_of_regionOwns hr
  have hsc := inCell_of_regionOwns hs'
  have hrr := cell_range hrc p.1.isLt
  have hss := cell_range hsc p.2.isLt
  have hrs0 : 0 < 2 * r * s := by nlinarith [hrr.1, hss.1]
  have hcos : 2 * r * s * sideCos r s d = r ^ 2 + s ^ 2 - d ^ 2 := by
    have hr0 : r ≠ 0 := by linarith [hrr.1]
    have hs0 : s ≠ 0 := by linarith [hss.1]
    unfold sideCos; field_simp
  have ht1 : -1 ≤ sideCos r s d := by
    have : -(2 * r * s) ≤ 2 * r * s * sideCos r s d := by rw [hcos]; nlinarith
    nlinarith
  have ht2 : sideCos r s d ≤ 1 := by
    have : 2 * r * s * sideCos r s d ≤ 2 * r * s := by rw [hcos]; nlinarith
    nlinarith
  have hreg : 2 * r * s * sideCos r s d < r * r + s * s - 49 / 16 := by
    rw [hcos]; nlinarith
  have := checkCellX_sound hg hcx hrc hsc ht1 ht2 hreg
  linarith

end D4Bound.KBN
