import D4Bound.V7CyclicNativeExtG
import D4Bound.V7CyclicNativeFullG
import D4Bound.CyclicNativeExtCorr
import D4Bound.CyclicNativeAllocLoSound

/-!
# Exterior cyclic cases: gauge in the polynomial, diagonal caps and sharper allocations

Same polynomial as `V7CyclicNativeExtG` (`extPolyG`), with the threshold `extThrW`
(`CyclicNativeExtCorr`): on pieces 5 and 6 the gauge bound `KBN.Ugen` drops the diagonal caps
correction `capsCorrection x x 1`, which is added back per box with weight `wX`
(`ungauged_le_gen_caps` from `V7CyclicNativeFullG`), and allocations use `allocProfLo2`.
`extW_case_of_check` proves the `outside` obligation for one case from one native check.
-/

namespace D4Bound.CyclicNative
open V7

lemma allocProfLo2_nonneg (c : AllocN) (qh : ℚ) : 0 ≤ allocProfLo2 c qh := by
  have h0 : 0 ≤ allocProfLo c qh := by
    unfold allocProfLo
    split_ifs <;> (try push_neg at *) <;> first | linarith | norm_num
  unfold allocProfLo2
  dsimp only
  split_ifs <;> first | exact h0 | exact le_trans (by norm_num) (le_max_left _ _)

lemma allocsLo2_sound (p q : ℕ) {rl rh sl sh qh : ℚ} {r s t : ℝ}
    (hr1 : (rl : ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl : ℝ) ≤ s) (hs2 : s ≤ sh)
    (hq : r*r+s*s+2*r*s*t ≤ qh) :
    ((((allocations.map toAllocN).map fun c => allocTermLo2 basisIntervals c p q rl rh sl sh qh).sum : ℚ) : ℝ)
      ≤ allocsCorrP p q r s t := by
  unfold allocsCorrP
  rw [List.map_map, PairPoly.rat_map_sum]
  apply list_sum_map_mono
  intro c hc
  obtain ⟨hw0, _, _⟩ := allocation_data_ok c hc
  have hw : (0:ℝ) ≤ c.weight := by exact_mod_cast hw0
  simp only [Function.comp_apply]
  unfold allocTermLo2
  rw [if_pos (show (0:ℚ) ≤ (toAllocN c).weight from hw0)]
  have a1 := radialLo_sound c.vector p hr1 hr2
  have a2 := radialLo_sound c.vector q hs1 hs2
  have b := allocProfLo2_sound c hq
  have nb : (0:ℝ) ≤ ((allocProfLo2 (toAllocN c) qh : ℚ) : ℝ) := by
    exact_mod_cast allocProfLo2_nonneg (toAllocN c) qh
  have hsum : ((max 0 (radialLo basisIntervals c.vector p rl rh) + max 0 (radialLo basisIntervals c.vector q sl sh) : ℚ) : ℝ)
      ≤ max 0 (pv c.vector p r) + max 0 (pv c.vector q s) := by
    push_cast
    exact add_le_add (max_le (le_max_left _ _) a1) (max_le (le_max_left _ _) a2)
  have hs0 : (0:ℝ) ≤ ((max 0 (radialLo basisIntervals c.vector p rl rh) + max 0 (radialLo basisIntervals c.vector q sl sh) : ℚ) : ℝ) := by
    push_cast; exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  have hwc : (toAllocN c).weight = c.weight := rfl
  have hvc : (toAllocN c).vector = c.vector := rfl
  rw [hwc, hvc]
  push_cast at hsum hs0 ⊢
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hw
  exact mul_le_mul hsum b nb (le_trans hs0 hsum)

end D4Bound.CyclicNative

namespace D4Bound.V7
open CyclicNative

/-- Weight of the diagonal caps of the side in region `p` (pieces 5 and 6 only). -/
def wX (p q : ℕ) : ℚ := if 5 ≤ p then cU p q else 0

def extCaseW (p q : ℕ) : ExtCaseW := ⟨extCaseG p q, wX p q, wX q p⟩

/-- Native check of one exterior case (improved threshold). -/
def extCheckW (u : Cap → Bool) (unit : ℚ) (fuel : ℕ) (p q : ℕ) : Bool :=
  checkPolyAff (extThrW (cdata u) xdata (extCaseW p q)) unit (extWidths (extCaseG p q)) fuel
    (extPolyG p q) (affOf (breaks.getD p 0, breaks.getD (p+1) 0))
    (affOf (breaks.getD q 0, breaks.getD (q+1) 0)) (affOf (0, 1))

noncomputable section

lemma cU_nonneg (p q : ℕ) : (0:ℝ) ≤ (cU p q : ℝ) := by
  obtain ⟨p0, p1⟩ := KBN.psiQ_range p
  obtain ⟨q0, _⟩ := KBN.psiQ_range q
  have : (0:ℚ) ≤ cU p q := by
    unfold cU
    have : 0 < 1 - KBN.psiQ p := by linarith
    positivity
  exact_mod_cast this

lemma wX_nonneg (p q : ℕ) : (0:ℝ) ≤ (wX p q : ℝ) := by
  unfold wX
  split_ifs
  · exact cU_nonneg p q
  · simp

def corrXW (p q : ℕ) (wr ws : ℚ) (r s z : ℝ) : ℝ :=
  corrX0 p q r s z + ((wr : ℝ) * capsCorrP p p r r 1 + (ws : ℝ) * capsCorrP q q s s 1)

lemma corrXW_nonneg (p q : ℕ) {wr ws : ℚ} (hwr : (0:ℝ) ≤ wr) (hws : (0:ℝ) ≤ ws) (r s z : ℝ) :
    0 ≤ corrXW p q wr ws r s z := by
  unfold corrXW
  have := corrX0_nonneg p q r s z
  have := mul_nonneg hwr (capsCorrP_nonneg p p r r 1)
  have := mul_nonneg hws (capsCorrP_nonneg q q s s 1)
  linarith

lemma ext_thr_soundW (p q : ℕ) (u : Cap → Bool) (ap bp aq bq : ℚ) (wr ws : ℚ)
    (hwr : (0:ℝ) ≤ wr) (hws : (0:ℝ) ≤ ws)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) ≤ bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) ≤ bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (B : Box) (hB : B.Valid) (x y z : ℝ) (hc : Cube x y z) :
    ((extThrW (cdata u) xdata ⟨⟨p,q,(ap,bp),(aq,bq),0⟩, wr, ws⟩ B : ℚ) : ℝ) ≤
      (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) * ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y))^18 *
      corrXW p q wr ws ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y)
        (B.c.pt z) := by
  obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
  obtain ⟨ha, hb, hcc⟩ := hB
  obtain ⟨cr1, cr2, lr0, r1, r7⟩ := box_coord pa1 pab pb7 ha hx0 hx1
  obtain ⟨cs1, cs2, ls0, s1, s7⟩ := box_coord qa1 qab qb7 hb hy0 hy1
  obtain ⟨uz0, uz1⟩ := Dy.pt_unit hcc hz0 hz1
  obtain ⟨lz, hz⟩ := Dy.pt_mem B.c hz0 hz1
  have zl0 : (0:ℝ) ≤ ((B.c.lo : ℚ) : ℝ) := by
    have : (0:ℚ) ≤ B.c.lo := by unfold Dy.lo; positivity
    exact_mod_cast this
  generalize (ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x = r' at *
  generalize (aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y = s' at *
  generalize B.c.pt z = z' at *
  have hrl1 : (1:ℝ) ≤ ((coordLo (ap,bp) B.a : ℚ) : ℝ) := by
    simp only [coordLo]; push_cast
    have : (0:ℝ) ≤ ((B.a.lo : ℚ) : ℝ) := by
      have : (0:ℚ) ≤ B.a.lo := by unfold Dy.lo; positivity
      exact_mod_cast this
    nlinarith
  have hsl1 : (1:ℝ) ≤ ((coordLo (aq,bq) B.b : ℚ) : ℝ) := by
    simp only [coordLo]; push_cast
    have : (0:ℝ) ≤ ((B.b.lo : ℚ) : ℝ) := by
      have : (0:ℚ) ≤ B.b.lo := by unfold Dy.lo; positivity
      exact_mod_cast this
    nlinarith
  have tb := extT_bounds hrl1 hsl1 cr1 cr2 cs1 cs2 zl0 lz hz
  have ta := extT_abs r1 r7 s1 s7 uz0 uz1
  have k1 := capsLo_sound u p q cr1 cr2 cs1 cs2 tb.1 tb.2 ta.1 ta.2
  have k2 := tentsLo_sound p q (by linarith) (by linarith) cr1 cr2 cs1 cs2 tb.1 tb.2
  have k3 := graphsLo_sound cr1 cr2 cs1 cs2 tb.1 tb.2
  have k4 := allocsLo2_sound p q cr1 cr2 cs1 cs2 (sqDist_le hrl1 hsl1 cr1 cr2 cs1 cs2 uz0 hz)
  have one1 : ((1:ℚ):ℝ) ≤ (1:ℝ) := by norm_num
  have one2 : (1:ℝ) ≤ ((1:ℚ):ℝ) := by norm_num
  have j1 := mul_le_mul_of_nonneg_left
    (capsLo_sound u p p cr1 cr2 cr1 cr2 one1 one2 (by norm_num) le_rfl) hwr
  have j2 := mul_le_mul_of_nonneg_left
    (capsLo_sound u q q cs1 cs2 cs1 cs2 one1 one2 (by norm_num) le_rfl) hws
  set W : ExtCaseW := ⟨⟨p,q,(ap,bp),(aq,bq),0⟩, wr, ws⟩ with hW
  have hcorr : ((extCorrLoW (cdata u) xdata W B : ℚ) : ℝ) ≤ corrXW p q wr ws r' s' z' := by
    simp only [cdata] at k1 j1 j2
    simp only [extCorrLoW, hW, xdata, cdata, Rat.cast_add, Rat.cast_mul, add_zero]
    unfold corrXW corrX0
    linarith
  have hcorr0 : ((max 0 (extCorrLoW (cdata u) xdata W B) : ℚ) : ℝ) ≤ corrXW p q wr ws r' s' z' := by
    push_cast
    exact max_le (corrXW_nonneg p q hwr hws _ _ _) hcorr
  have hm0 : (0:ℝ) ≤ ((max 0 (extCorrLoW (cdata u) xdata W B) : ℚ) : ℝ) := by
    push_cast; exact le_max_left _ _
  have h1 : (0:ℝ) < coordLo (ap, bp) B.a := by exact_mod_cast lr0
  have h2 : (0:ℝ) < coordLo (aq, bq) B.b := by exact_mod_cast ls0
  have hfac : (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) * ((coordLo (aq, bq) B.b : ℚ) : ℝ))^18 ≤
      (2 * r' * s')^18 := by
    apply pow_le_pow_left₀ (by positivity)
    have e1 := mul_le_mul cr1 cs1 h2.le (by linarith)
    nlinarith
  have hthr : ((extThrW (cdata u) xdata W B : ℚ) : ℝ) = (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) *
      ((coordLo (aq, bq) B.b : ℚ) : ℝ))^18 * ((max 0 (extCorrLoW (cdata u) xdata W B) : ℚ) : ℝ) := by
    simp only [extThrW, hW]; push_cast; ring
  rw [hthr]
  exact mul_le_mul hfac hcorr0 hm0 (pow_nonneg (by positivity) _)

/-- One side of the gauge: `-(cU k a) U_k + wX k a * caps(x,x,1) ≤ -(cU k a) ungaugedPair x`. -/
lemma side_gaugeX (hs : KBN.scalarCheck = true) (ha : KBN.gaugeAllOK = true) {k a : ℕ}
    (hk : k < 7) {x : ℝ} (hx : RegionOwns k x) :
    -((cU k a : ℝ) * KBN.E1 (KBN.Ugen k) (x - 1)) + (wX k a : ℝ) * capsCorrection x x 1 ≤
      -((cU k a : ℝ) * ungaugedPair x) := by
  simp only [KBN.gaugeAllOK, Bool.and_eq_true] at ha
  obtain ⟨hs56, hall⟩ := ha
  have hk' := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk'
  have hok := hk'.1.1
  have hcut : k < 5 → KBN.capsCutOK k = true := fun h5 => hk'.1.2.resolve_left (by omega)
  have cx := KBN.inCell_of_regionOwns hx
  have hc := cU_nonneg k a
  unfold wX
  by_cases h5 : 5 ≤ k
  · rw [if_pos h5]
    have U := ungauged_le_gen_caps hs56 hk h5 cx hok
    have m := mul_le_mul_of_nonneg_left U hc
    rw [mul_sub] at m
    linarith
  · rw [if_neg h5]
    have U := KBN.ungauged_le_gen hs hs56 hk cx hok hcut
    have m := mul_le_mul_of_nonneg_left U hc
    push_cast
    linarith

/-- Gauge part of `-pair` bounded below by the polynomial terms and the diagonal caps. -/
lemma gauge_le_UW (hs : KBN.scalarCheck = true) (ha : KBN.gaugeAllOK = true) {p q : ℕ}
    (hp : p < 7) (hq : q < 7) {r s : ℝ} (hr : RegionOwns p r) (hsr : RegionOwns q s) :
    -((cU p q : ℝ) * KBN.E1 (KBN.Ugen p) (r - 1) + (cU q p : ℝ) * KBN.E1 (KBN.Ugen q) (s - 1)) +
      ((wX p q : ℝ) * capsCorrection r r 1 + (wX q p : ℝ) * capsCorrection s s 1) ≤
      (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 := by
  have ha' := ha
  simp only [KBN.gaugeAllOK, Bool.and_eq_true] at ha'
  have fac : ∀ k < 7, KBN.cellOK k = true := by
    intro k hk
    have h := List.all_eq_true.mp ha'.2 k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have pr := KBN.gaugePsi_cell (fac p hp) (KBN.inCell_of_regionOwns hr)
  have ps := KBN.gaugePsi_cell (fac q hq) (KBN.inCell_of_regionOwns hsr)
  have A := side_gaugeX (a := q) hs ha hp hr
  have B := side_gaugeX (a := p) hs ha hq hsr
  obtain ⟨p0, p1⟩ := KBN.psiQ_range p
  obtain ⟨q0, q1⟩ := KBN.psiQ_range q
  have p1' : (0 : ℝ) < 1 - KBN.psiQ p := by
    have : (KBN.psiQ p : ℝ) < 1 := by exact_mod_cast p1
    linarith
  have q1' : (0 : ℝ) < 1 - KBN.psiQ q := by
    have : (KBN.psiQ q : ℝ) < 1 := by exact_mod_cast q1
    linarith
  have e : (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 =
      -((cU p q : ℝ) * ungaugedPair r + (cU q p : ℝ) * ungaugedPair s) := by
    unfold gaugeWeight cU
    rw [pr, ps]
    push_cast
    field_simp
    ring
  rw [e]
  linarith

theorem extW_case_of_check (hsc : KBN.scalarCheck = true) (hga : KBN.gaugeAllOK = true)
    (p q : ℕ) (hp : p < 7) (hq : q < 7) (u : Cap → Bool) (unit : ℚ) (fuel : ℕ)
    (h : extCheckW u unit fuel p q = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : 7/4 < d) (htri : d ≤ r+s) :
    pair r s (sideCos r s d) ≤ 0 := by
  have hwr := wX_nonneg p q
  have hws := wX_nonneg q p
  obtain ⟨pa1, pab, pb7⟩ := breaks_range hp
  obtain ⟨qa1, qab, qb7⟩ := breaks_range hq
  have hrb := region_bounds hr
  have hsb := region_bounds hs
  unfold extCheckW extCaseW extCaseG at h
  generalize breaks.getD p 0 = ap at h hrb pa1 pab
  generalize breaks.getD (p+1) 0 = bp at h hrb pab pb7
  generalize breaks.getD q 0 = aq at h hsb qa1 qab
  generalize breaks.getD (q+1) 0 = bq at h hsb qab qb7
  let G : ℝ → ℝ → ℝ → ℝ := fun x y z =>
    (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * x) * ((aq:ℝ) + ((bq:ℝ) - aq) * y))^18 *
    corrXW p q (wX p q) (wX q p) ((ap:ℝ) + ((bp:ℝ) - ap) * x) ((aq:ℝ) + ((bq:ℝ) - aq) * y) z
  have hG : ∀ x y z, Cube x y z → 0 ≤ G x y z := by
    intro x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    have e1 : (0:ℝ) ≤ ((bp:ℝ) - ap) * x := mul_nonneg (by linarith) hx0
    have e2 : (0:ℝ) ≤ ((bq:ℝ) - aq) * y := mul_nonneg (by linarith) hy0
    have f1 : (0:ℝ) ≤ (ap:ℝ) + ((bp:ℝ) - ap) * x := by linarith
    have f2 : (0:ℝ) ≤ (aq:ℝ) + ((bq:ℝ) - aq) * y := by linarith
    exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) f1) f2) _)
      (corrXW_nonneg p q hwr hws _ _ _)
  have hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((extThrW (cdata u) xdata ⟨⟨p, q, (ap, bp), (aq, bq), 0⟩, wX p q, wX q p⟩ B : ℚ) : ℝ) ≤
        G (B.a.pt x) (B.b.pt y) (B.c.pt z) :=
    fun B hB x y z hc => ext_thr_soundW p q u ap bp aq bq (wX p q) (wX q p) hwr hws
      pa1 pab.le pb7 qa1 qab.le qb7 B hB x y z hc
  have hsound := checkPolyAff_sound _ unit _ fuel _ _ _ _ G h hthr hG
  have hpx : (0:ℝ) < (bp:ℝ) - ap := by linarith
  have hpy : (0:ℝ) < (bq:ℝ) - aq := by linarith
  have r1 : 1 ≤ r := by linarith [hrb.1]
  have s1 : 1 ≤ s := by linarith [hsb.1]
  have r7 : r ≤ 7/4 := by linarith [hrb.2]
  have s7 : s ≤ 7/4 := by linarith [hsb.2]
  obtain ⟨hz0, hz1, hzt⟩ := exterior_coordinate r1 s1 hd htri
  set z := ((r+s)^2-d^2)/((r+s)^2-(7/4)^2)
  set x := (r - ap)/((bp:ℝ) - ap)
  set y := (s - aq)/((bq:ℝ) - aq)
  have hcube : Cube x y z := by
    refine ⟨div_nonneg (by linarith) hpx.le, ?_, div_nonneg (by linarith) hpy.le, ?_, hz0, hz1⟩
    · rw [div_le_one hpx]; linarith
    · rw [div_le_one hpy]; linarith
  have hRx : (ap:ℝ) + ((bp:ℝ) - ap) * x = r := by simp only [x]; field_simp; ring
  have hSy : (aq:ℝ) + ((bq:ℝ) - aq) * y = s := by simp only [y]; field_simp; ring
  have hb := hsound x y z hcube
  rw [affOf_eval, affOf_eval, affOf_eval] at hb
  simp only [G, hRx, hSy] at hb
  have hz' : ((0:ℚ):ℝ) + (((1:ℚ):ℝ) - ((0:ℚ):ℝ)) * z = z := by push_cast; ring
  rw [hz'] at hb
  have eA := eval_extA (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1) r s z
  have eB := eval_extB (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1) r s z
  simp only [CyclicPoly.eval_coordinate0, CyclicPoly.eval_coordinate1] at eA eB
  have hBne : CyclicPoly.eval (extB (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1)) r s z ≠ 0 := by
    rw [eB]; positivity
  have he := CyclicPoly.eval_pair (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1)
    (extA (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1))
    (extB (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1))
    r s z (by simpa using r1) (by simpa using r7) (by simpa using s1) (by simpa using s7) hBne
  simp only [CyclicPoly.eval_coordinate0, CyclicPoly.eval_coordinate1] at he
  rw [radial_piece_of_region hr, radial_piece_of_region hs, eA, eB] at he
  have ht : (-(2*r*s) + z*((r+s)^2 - 49/16)) / (2*r*s) = sideCos r s d := by
    unfold sideCos; rw [hzt]; field_simp; ring
  rw [ht] at he
  have hU := eval_p1N (KBN.Ugen p) r s z
  have hV := eval_p1N (KBN.Ugen q) r s z
  have hpoly : CyclicPoly.eval (extPolyG p q) r s z =
      (2*r*s)^18 * (polynomialPair r s (sideCos r s d) +
        ((cU p q : ℝ) * KBN.E1 (KBN.Ugen p) (r - 1) + (cU q p : ℝ) * KBN.E1 (KBN.Ugen q) (s - 1))) := by
    rw [extPolyG, NPoly.fastAdd_eq, CyclicPoly.eval_fastAdd, extPolyU, NPoly.pair_eq,
      NPoly.coordinate_eq, he, gaugeN]
    simp only [NPoly.fastMul_eq, NPoly.fastPower_eq, NPoly.fastAdd_eq, NPoly.scale_eq,
      NPoly.coordinate_eq, CyclicPoly.eval_fastMul, CyclicPoly.eval_fastPower,
      CyclicPoly.eval_fastAdd, CyclicPoly.eval_scale, eB, hU.1, hV.2]
    ring
  rw [hpoly] at hb
  have hfpos : 0 < (2*r*s)^18 := by positivity
  have hle := le_of_mul_le_mul_left hb hfpos
  have hT : extT r s z = sideCos r s d := by unfold extT sideCos; rw [hzt]; ring
  unfold corrXW corrX0 at hle
  rw [hT] at hle
  have hpr := radial_piece_of_region hr
  have hps := radial_piece_of_region hs
  have c1 : capsCorrP p q r s (sideCos r s d) = capsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact capsCorrP_eq r1 r7 s1 s7 _
  have c2 : tentsCorrP p q r s (sideCos r s d) = tentsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact tentsCorrP_eq r1 r7 s1 s7 _
  have c3 : allocsCorrP p q r s (sideCos r s d) = allocationsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact allocsCorrP_eq r1 r7 s1 s7 _
  have c4 : capsCorrP p p r r 1 = capsCorrection r r 1 := by
    rw [← hpr]; exact capsCorrP_eq r1 r7 r1 r7 _
  have c5 : capsCorrP q q s s 1 = capsCorrection s s 1 := by
    rw [← hps]; exact capsCorrP_eq s1 s7 s1 s7 _
  rw [c1, c2, c3, c4, c5] at hle
  have g := gauge_le_UW hsc hga hp hq hr hs
  rw [pair_split]
  unfold otherCorr
  linarith

end
end D4Bound.V7

#print axioms D4Bound.V7.extW_case_of_check
