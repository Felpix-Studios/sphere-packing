import D4Bound.V7CyclicNativeExt
import D4Bound.V7CyclicNativeFullAff
import D4Bound.KBNGaugeCheck

/-!
# Exterior cyclic cases with the gauge inside the polynomial

The cyclic agent's exterior route (`V7CyclicNativeExt`) with two changes, by p-146b5edd705c:
the polynomial is built in the original radii and shifted by `checkPolyAff` (as in
`V7CyclicNativeFullAff`), and the gauge term is not a constant credit: the polynomial upper
bound `KBN.Ugen` of the ungauged diagonal source (`KBN.ungauged_le_gen`, all seven pieces) is
added to the polynomial, multiplied by `(2rs)^18`, so the gauge is exact to `ghat` accuracy
and fully correlated with the pair polynomial. `extG_case_of_check` proves the `outside`
obligation for one case from one native check.
-/
namespace D4Bound.V7
open CyclicNative

/-- `x - 1` in coordinate `i`. -/
def uN (i : Fin 3) : NPoly.Poly := NPoly.fastAdd (NPoly.coordinate i) (NPoly.constant (-1))

/-- A one-variable polynomial in `x - 1` (constant term first) as a sparse polynomial. -/
def p1N (c : List ℚ) (i : Fin 3) : NPoly.Poly :=
  c.foldr (fun a acc => NPoly.fastAdd (NPoly.constant a) (NPoly.fastMul (uN i) acc)) []

def cU (p q : ℕ) : ℚ := KBN.psiQ q / (1 - KBN.psiQ p) / 2

def extPolyU (p q : ℕ) : NPoly.Poly :=
  NPoly.pair NPoly.kdata p q (NPoly.coordinate 0) (NPoly.coordinate 1)
    (extA (NPoly.coordinate 0) (NPoly.coordinate 1)) (extB (NPoly.coordinate 0) (NPoly.coordinate 1))

def gaugeN (p q : ℕ) : NPoly.Poly :=
  NPoly.fastMul (NPoly.fastPower (extB (NPoly.coordinate 0) (NPoly.coordinate 1)) 18)
    (NPoly.fastAdd (NPoly.scale (cU p q) (p1N (KBN.Ugen p) 0))
      (NPoly.scale (cU q p) (p1N (KBN.Ugen q) 1)))

def extPolyG (p q : ℕ) : NPoly.Poly := NPoly.fastAdd (extPolyU p q) (gaugeN p q)

def extCaseG (p q : ℕ) : ExtCase :=
  ⟨p, q, (breaks.getD p 0, breaks.getD (p+1) 0), (breaks.getD q 0, breaks.getD (q+1) 0), 0⟩

/-- Native check of one exterior case. -/
def extCheckG (u : Cap → Bool) (unit : ℚ) (fuel : ℕ) (p q : ℕ) : Bool :=
  checkPolyAff (extThr (cdata u) xdata (extCaseG p q)) unit (extWidths (extCaseG p q)) fuel
    (extPolyG p q) (affOf (breaks.getD p 0, breaks.getD (p+1) 0))
    (affOf (breaks.getD q 0, breaks.getD (q+1) 0)) (affOf (0, 1))

noncomputable section

theorem eval_p1N (c : List ℚ) (x y z : ℝ) :
    CyclicPoly.eval (p1N c 0) x y z = KBN.E1 c (x - 1) ∧
    CyclicPoly.eval (p1N c 1) x y z = KBN.E1 c (y - 1) := by
  induction c with
  | nil => simp [p1N, KBN.E1, CyclicPoly.eval]
  | cons a c ih =>
    simp only [p1N, List.foldr_cons] at ih ⊢
    simp only [NPoly.fastAdd_eq, NPoly.fastMul_eq, NPoly.constant_eq, uN, NPoly.coordinate_eq,
      CyclicPoly.eval_fastAdd, CyclicPoly.eval_fastMul, CyclicPoly.eval_constant,
      CyclicPoly.eval_coordinate0, CyclicPoly.eval_coordinate1] at ih ⊢
    simp only [KBN.E1, KBN.peval_cons] at ih ⊢
    rw [ih.1, ih.2]
    push_cast
    constructor <;> ring

def corrX0 (p q : ℕ) (r s z : ℝ) : ℝ :=
  capsCorrP p q r s (extT r s z) + tentsCorrP p q r s (extT r s z) +
    graphsCorrection r s (extT r s z) + allocsCorrP p q r s (extT r s z)

lemma corrX0_nonneg (p q : ℕ) (r s z : ℝ) : 0 ≤ corrX0 p q r s z := by
  unfold corrX0
  have := capsCorrP_nonneg p q r s (extT r s z)
  have := tentsCorrP_nonneg p q r s (extT r s z)
  have := graphsCorrection_nonneg r s (extT r s z)
  have := allocsCorrP_nonneg p q r s (extT r s z)
  linarith

lemma ext_thr_sound0 (p q : ℕ) (u : Cap → Bool) (ap bp aq bq : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) ≤ bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) ≤ bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (B : Box) (hB : B.Valid) (x y z : ℝ) (hc : Cube x y z) :
    ((extThr (cdata u) xdata ⟨p,q,(ap,bp),(aq,bq),0⟩ B : ℚ) : ℝ) ≤
      (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) * ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y))^18 *
      corrX0 p q ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y) (B.c.pt z) := by
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
  have k4 := allocsLo_sound p q cr1 cr2 cs1 cs2 (sqDist_le hrl1 hsl1 cr1 cr2 cs1 cs2 uz0 hz)
  set E : ExtCase := ⟨p,q,(ap,bp),(aq,bq),0⟩ with hE
  have hcorr : ((extCorrLo (cdata u) xdata E B : ℚ) : ℝ) ≤ corrX0 p q r' s' z' := by
    simp only [cdata] at k1
    simp only [extCorrLo, hE, xdata, cdata, Rat.cast_add, Rat.cast_zero, add_zero]
    unfold corrX0
    linarith
  have hcorr0 : ((max 0 (extCorrLo (cdata u) xdata E B) : ℚ) : ℝ) ≤ corrX0 p q r' s' z' := by
    push_cast
    exact max_le (corrX0_nonneg p q _ _ _) hcorr
  have hm0 : (0:ℝ) ≤ ((max 0 (extCorrLo (cdata u) xdata E B) : ℚ) : ℝ) := by
    push_cast; exact le_max_left _ _
  have h1 : (0:ℝ) < coordLo (ap, bp) B.a := by exact_mod_cast lr0
  have h2 : (0:ℝ) < coordLo (aq, bq) B.b := by exact_mod_cast ls0
  have hfac : (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) * ((coordLo (aq, bq) B.b : ℚ) : ℝ))^18 ≤
      (2 * r' * s')^18 := by
    apply pow_le_pow_left₀ (by positivity)
    have e1 := mul_le_mul cr1 cs1 h2.le (by linarith)
    nlinarith
  have hthr : ((extThr (cdata u) xdata E B : ℚ) : ℝ) = (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) *
      ((coordLo (aq, bq) B.b : ℚ) : ℝ))^18 * ((max 0 (extCorrLo (cdata u) xdata E B) : ℚ) : ℝ) := by
    simp only [extThr, hE]; push_cast; ring
  rw [hthr]
  exact mul_le_mul hfac hcorr0 hm0 (pow_nonneg (by positivity) _)

/-- Gauge part of `-pair` bounded below by the polynomial terms. -/
lemma gauge_le_U (hs : KBN.scalarCheck = true) (ha : KBN.gaugeAllOK = true) {p q : ℕ}
    (hp : p < 7) (hq : q < 7) {r s : ℝ} (hr : RegionOwns p r) (hsr : RegionOwns q s) :
    -((cU p q : ℝ) * KBN.E1 (KBN.Ugen p) (r - 1) + (cU q p : ℝ) * KBN.E1 (KBN.Ugen q) (s - 1)) ≤
      (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 := by
  simp only [KBN.gaugeAllOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ha
  obtain ⟨hs56, hall⟩ := ha
  have fac : ∀ k < 7, KBN.cellOK k = true ∧ (k < 5 → KBN.capsCutOK k = true) := by
    intro k hk
    have h := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, fun h5 => h.1.2.resolve_left (by omega)⟩
  have cr := KBN.inCell_of_regionOwns hr
  have cs := KBN.inCell_of_regionOwns hsr
  have Ur := KBN.ungauged_le_gen hs hs56 hp cr (fac p hp).1 (fac p hp).2
  have Us := KBN.ungauged_le_gen hs hs56 hq cs (fac q hq).1 (fac q hq).2
  have pr := KBN.gaugePsi_cell (fac p hp).1 cr
  have ps := KBN.gaugePsi_cell (fac q hq).1 cs
  obtain ⟨p0, p1⟩ := KBN.psiQ_range p
  obtain ⟨q0, q1⟩ := KBN.psiQ_range q
  have p0' : (0 : ℝ) ≤ KBN.psiQ p := by exact_mod_cast p0
  have q0' : (0 : ℝ) ≤ KBN.psiQ q := by exact_mod_cast q0
  have p1' : (0 : ℝ) < 1 - KBN.psiQ p := by
    have : (KBN.psiQ p : ℝ) < 1 := by exact_mod_cast p1
    linarith
  have q1' : (0 : ℝ) < 1 - KBN.psiQ q := by
    have : (KBN.psiQ q : ℝ) < 1 := by exact_mod_cast q1
    linarith
  unfold gaugeWeight cU
  rw [pr, ps]
  push_cast
  have c1 : (0 : ℝ) ≤ (KBN.psiQ q : ℝ) / (1 - KBN.psiQ p) / 2 := by positivity
  have c2 : (0 : ℝ) ≤ (KBN.psiQ p : ℝ) / (1 - KBN.psiQ q) / 2 := by positivity
  have k1 := mul_le_mul_of_nonneg_left Ur c1
  have k2 := mul_le_mul_of_nonneg_left Us c2
  have e : (-ungaugedPair r / (1 - (KBN.psiQ p : ℝ)) * KBN.psiQ q +
      -ungaugedPair s / (1 - (KBN.psiQ q : ℝ)) * KBN.psiQ p) / 2 =
      -((KBN.psiQ q : ℝ) / (1 - KBN.psiQ p) / 2 * ungaugedPair r +
        (KBN.psiQ p : ℝ) / (1 - KBN.psiQ q) / 2 * ungaugedPair s) := by
    ring
  rw [e]
  linarith

theorem extG_case_of_check (hsc : KBN.scalarCheck = true) (hga : KBN.gaugeAllOK = true)
    (p q : ℕ) (hp : p < 7) (hq : q < 7) (u : Cap → Bool) (unit : ℚ) (fuel : ℕ)
    (h : extCheckG u unit fuel p q = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : 7/4 < d) (htri : d ≤ r+s) :
    pair r s (sideCos r s d) ≤ 0 := by
  obtain ⟨pa1, pab, pb7⟩ := breaks_range hp
  obtain ⟨qa1, qab, qb7⟩ := breaks_range hq
  have hrb := region_bounds hr
  have hsb := region_bounds hs
  unfold extCheckG extCaseG at h
  generalize breaks.getD p 0 = ap at h hrb pa1 pab
  generalize breaks.getD (p+1) 0 = bp at h hrb pab pb7
  generalize breaks.getD q 0 = aq at h hsb qa1 qab
  generalize breaks.getD (q+1) 0 = bq at h hsb qab qb7
  let G : ℝ → ℝ → ℝ → ℝ := fun x y z =>
    (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * x) * ((aq:ℝ) + ((bq:ℝ) - aq) * y))^18 *
    corrX0 p q ((ap:ℝ) + ((bp:ℝ) - ap) * x) ((aq:ℝ) + ((bq:ℝ) - aq) * y) z
  have hG : ∀ x y z, Cube x y z → 0 ≤ G x y z := by
    intro x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    have e1 : (0:ℝ) ≤ ((bp:ℝ) - ap) * x := mul_nonneg (by linarith) hx0
    have e2 : (0:ℝ) ≤ ((bq:ℝ) - aq) * y := mul_nonneg (by linarith) hy0
    have f1 : (0:ℝ) ≤ (ap:ℝ) + ((bp:ℝ) - ap) * x := by linarith
    have f2 : (0:ℝ) ≤ (aq:ℝ) + ((bq:ℝ) - aq) * y := by linarith
    exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) f1) f2) _) (corrX0_nonneg p q _ _ _)
  have hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((extThr (cdata u) xdata ⟨p, q, (ap, bp), (aq, bq), 0⟩ B : ℚ) : ℝ) ≤
        G (B.a.pt x) (B.b.pt y) (B.c.pt z) :=
    fun B hB x y z hc => ext_thr_sound0 p q u ap bp aq bq pa1 pab.le pb7 qa1 qab.le qb7 B hB x y z hc
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
  unfold corrX0 at hle
  rw [hT] at hle
  have hpr := radial_piece_of_region hr
  have hps := radial_piece_of_region hs
  have c1 : capsCorrP p q r s (sideCos r s d) = capsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact capsCorrP_eq r1 r7 s1 s7 _
  have c2 : tentsCorrP p q r s (sideCos r s d) = tentsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact tentsCorrP_eq r1 r7 s1 s7 _
  have c3 : allocsCorrP p q r s (sideCos r s d) = allocationsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact allocsCorrP_eq r1 r7 s1 s7 _
  rw [c1, c2, c3] at hle
  have g := gauge_le_U hsc hga hp hq hr hs
  rw [pair_split]
  unfold otherCorr
  linarith

end
end D4Bound.V7

#print axioms D4Bound.V7.extG_case_of_check
