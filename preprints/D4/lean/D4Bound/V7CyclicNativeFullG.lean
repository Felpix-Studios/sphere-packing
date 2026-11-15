import D4Bound.V7CyclicNativeFullAff
import D4Bound.KBNGaugeCheck
import D4Bound.CyclicNativeFullGThr

/-!
# Full cyclic cases with the gauge inside the polynomial

Same route as `V7CyclicNativeFullAff` (unshifted polynomial, affine maps inside the checker,
caps bounded per box), but the gauge charge is not a constant credit. The polynomial upper
bound `KBN.Ugen k` of the ungauged diagonal source (`KBN.ungauged_le_gen`, all seven pieces)
enters the polynomial, multiplied by `(2rsd)^18`, with coefficient
`cF p q k = (ψ_q + ψ_k)/(1 - ψ_p)/2`. So the gauge is exact to `ghat` accuracy on every
piece, including pieces 3 to 6 where the constant credit was 0. On pieces 5 and 6 `Ugen`
drops the diagonal caps correction `capsCorrection x x 1`; the threshold `fullThrG` adds a
box lower bound of it back with weight `wF` (`ungauged_le_gen_caps`). Otherwise the
threshold uses the pair caps only.
-/
namespace D4Bound.V7
open CyclicNative

/-- `x - 1` in coordinate `i`. -/
def uF (i : Fin 3) : NPoly.Poly := NPoly.fastAdd (NPoly.coordinate i) (NPoly.constant (-1))

/-- A one-variable polynomial in `x - 1` (constant term first) as a sparse polynomial. -/
def p1F (c : List ℚ) (i : Fin 3) : NPoly.Poly :=
  c.foldr (fun a acc => NPoly.fastAdd (NPoly.constant a) (NPoly.fastMul (uF i) acc)) []

/-- Coefficient of `U_p(r - 1)`: `(ψ_q + ψ_k)/(1 - ψ_p)/2`. -/
def cF (p q k : ℕ) : ℚ := (KBN.psiQ q + KBN.psiQ k) / (1 - KBN.psiQ p) / 2

/-- `2rsd` in the original radii. -/
def factorF : NPoly.Poly :=
  NPoly.scale 2 (NPoly.fastMul (NPoly.fastMul (NPoly.coordinate 0) (NPoly.coordinate 1))
    (NPoly.coordinate 2))

def gaugeF (p q k : ℕ) : NPoly.Poly :=
  NPoly.fastMul (NPoly.fastPower factorF 18)
    (NPoly.fastAdd (NPoly.scale (cF p q k) (p1F (KBN.Ugen p) 0))
      (NPoly.fastAdd (NPoly.scale (cF q p k) (p1F (KBN.Ugen q) 1))
        (NPoly.scale (cF k p q) (p1F (KBN.Ugen k) 2))))

def fullPolyG (p q k : ℕ) : NPoly.Poly := NPoly.fastAdd (fullPolyU p q k) (gaugeF p q k)

/-- The case with zero constant gauge credit. -/
def fullCaseG (p q k : ℕ) : FullCase :=
  ⟨p, q, k, (breaks.getD p 0, breaks.getD (p+1) 0), (breaks.getD q 0, breaks.getD (q+1) 0),
    (breaks.getD k 0, breaks.getD (k+1) 0), 0⟩

/-- Weight of the diagonal caps of a side in region `p` (pieces 5 and 6 only). -/
def wF (p q k : ℕ) : ℚ := if 5 ≤ p then cF p q k else 0

def fullCaseGG (p q k : ℕ) : FullCaseG := ⟨fullCaseG p q k, wF p q k, wF q p k, wF k p q⟩

/-- Native check of one full case. -/
def fullCheckG (u : Cap → Bool) (unit : ℚ) (fuel : ℕ) (p q k : ℕ) : Bool :=
  checkPolyAff (fullThrG (cdata u) (fullCaseGG p q k)) unit (fullWidths (fullCaseG p q k)) fuel
    (fullPolyG p q k) (affOf (breaks.getD p 0, breaks.getD (p+1) 0))
    (affOf (breaks.getD q 0, breaks.getD (q+1) 0)) (affOf (breaks.getD k 0, breaks.getD (k+1) 0))

noncomputable section

theorem eval_p1F (c : List ℚ) (x y z : ℝ) :
    CyclicPoly.eval (p1F c 0) x y z = KBN.E1 c (x - 1) ∧
    CyclicPoly.eval (p1F c 1) x y z = KBN.E1 c (y - 1) ∧
    CyclicPoly.eval (p1F c 2) x y z = KBN.E1 c (z - 1) := by
  induction c with
  | nil => simp [p1F, KBN.E1, CyclicPoly.eval]
  | cons a c ih =>
    simp only [p1F, List.foldr_cons] at ih ⊢
    simp only [NPoly.fastAdd_eq, NPoly.fastMul_eq, NPoly.constant_eq, uF, NPoly.coordinate_eq,
      CyclicPoly.eval_fastAdd, CyclicPoly.eval_fastMul, CyclicPoly.eval_constant,
      CyclicPoly.eval_coordinate0, CyclicPoly.eval_coordinate1,
      CyclicPoly.eval_coordinate2] at ih ⊢
    simp only [KBN.E1, KBN.peval_cons] at ih ⊢
    rw [ih.1, ih.2.1, ih.2.2]
    push_cast
    refine ⟨by ring, by ring, by ring⟩

/-! ## Diagonal caps in the gauge bound on pieces 5 and 6 -/

theorem ungaugedPair_le_upper_caps {r : ℝ} (h1 : 1 ≤ r) (hR : r ≤ 7/4) :
    ungaugedPair r ≤ scalarRadius r + diagonalUpper r - capsCorrection r r 1 := by
  have h := rawLinear_le_uncut h1 hR
  have ht := tentsCorrection_nonneg h1 h1 hR hR (1 : ℝ)
  have ha := allocationsCorrection_nonneg h1 h1 hR hR (1 : ℝ)
  have hg := graphsCorrection_nonneg r r 1
  unfold ungaugedPair rawPair diagonalUpper
  linarith

theorem ungauged_le_U_caps {g : KBN.P1} {k : ℕ} {r : ℝ} (h : KBN.RadOK k r)
    (hg : scalarRadius r ≤ KBN.E1 g (r - 1)) :
    ungaugedPair r ≤ KBN.E1 (KBN.UpolyU g k) (r - 1) - capsCorrection r r 1 := by
  have hr := KBN.cell_range h.hr h.k7
  have hcp : KBN.CellPair k k r r := ⟨h.hr, h.hr, h.pr, h.pr, h.k7, h.k7, h.ok, h.ok⟩
  have hcore : KBN.E1 (KBN.diag3 (KBN.coreP k k)) (r - 1) = KBN.corePair r r 1 := by
    rw [KBN.E1_diag3]; exact KBN.E3_coreP hcp 1
  have hU := ungaugedPair_le_upper_caps hr.1 hr.2
  have e : diagonalUpper r = 2 * uncutLinear r + KBN.corePair r r 1 := by
    unfold diagonalUpper KBN.corePair; ring
  unfold KBN.UpolyU
  simp only [KBN.E1_add, KBN.E1_smul, hcore, KBN.E1_linPU h]
  rw [e] at hU
  push_cast
  linarith

/-- On pieces 5 and 6 the gauge polynomial bound keeps the diagonal caps. -/
theorem ungauged_le_gen_caps (hs56 : KBN.scalarCheck56 = true) {k : ℕ} {r : ℝ} (hk : k < 7)
    (h5 : 5 ≤ k) (hr : KBN.InCell k r) (hok : KBN.cellOK k = true) :
    ungaugedPair r ≤ KBN.E1 (KBN.Ugen k) (r - 1) - capsCorrection r r 1 := by
  have pr := KBN.radialPiece_cell7 hr hk
  obtain ⟨h1, h2, h3⟩ := hr
  unfold KBN.Ugen
  rw [if_neg (by omega)]
  simp only [KBN.scalarCheck56, Bool.and_eq_true] at hs56
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hs56
  by_cases h55 : k = 5
  · subst h55
    rw [if_pos rfl]
    have hb1 : (102597 / 100000 : ℝ) ≤ r := by simpa [KBN.cellLo, breaks] using h1
    have hb2 : r ≤ 3 / 2 := by simpa [KBN.cellHi, breaks] using h2
    apply ungauged_le_U_caps ⟨⟨h1, h2, h3⟩, pr, hk, hok⟩
    by_cases hm : r - 1 ≤ ((2 / 5 : ℚ) : ℝ)
    · exact KBN.segCheck_sound a (by push_cast; linarith) hm
    · exact KBN.segCheck_sound b (by push_cast at hm ⊢; linarith) (by push_cast; linarith)
  · have h66 : k = 6 := by omega
    subst h66
    rw [if_neg (by norm_num)]
    have hb1 : (3 / 2 : ℝ) ≤ r := by simpa [KBN.cellLo, breaks] using h1
    have hb2 : r ≤ 7 / 4 := by simpa [KBN.cellHi, breaks] using h2
    apply ungauged_le_U_caps ⟨⟨h1, h2, h3⟩, pr, hk, hok⟩
    by_cases hm : r - 1 ≤ ((7 / 10 : ℚ) : ℝ)
    · exact KBN.segCheck_sound c (by push_cast; linarith) hm
    · exact KBN.segCheck_sound d (by push_cast at hm ⊢; linarith) (by push_cast; linarith)

lemma cF_nonneg (p q k : ℕ) : (0:ℝ) ≤ (cF p q k : ℝ) := by
  obtain ⟨p0, p1⟩ := KBN.psiQ_range p
  obtain ⟨q0, _⟩ := KBN.psiQ_range q
  obtain ⟨k0, _⟩ := KBN.psiQ_range k
  have : (0:ℚ) ≤ cF p q k := by
    unfold cF
    have : 0 < 1 - KBN.psiQ p := by linarith
    positivity
  exact_mod_cast this

lemma wF_nonneg (p q k : ℕ) : (0:ℝ) ≤ (wF p q k : ℝ) := by
  unfold wF
  split_ifs
  · exact cF_nonneg p q k
  · simp

/-- One side of the gauge charge. -/
lemma side_gauge (hs : KBN.scalarCheck = true) (ha : KBN.gaugeAllOK = true) {k a b : ℕ}
    (hk : k < 7) {x : ℝ} (hx : RegionOwns k x) :
    -((cF k a b : ℝ) * KBN.E1 (KBN.Ugen k) (x - 1)) + (wF k a b : ℝ) * capsCorrection x x 1 ≤
      gaugeWeight x * ((KBN.psiQ a : ℝ) + KBN.psiQ b) / 2 := by
  simp only [KBN.gaugeAllOK, Bool.and_eq_true] at ha
  obtain ⟨hs56, hall⟩ := ha
  have hk' := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk'
  have hok := hk'.1.1
  have hcut : k < 5 → KBN.capsCutOK k = true := fun h5 => hk'.1.2.resolve_left (by omega)
  have cx := KBN.inCell_of_regionOwns hx
  have px := KBN.gaugePsi_cell hok cx
  obtain ⟨p0, p1⟩ := KBN.psiQ_range k
  have p1' : (0 : ℝ) < 1 - KBN.psiQ k := by
    have : (KBN.psiQ k : ℝ) < 1 := by exact_mod_cast p1
    linarith
  have hc := cF_nonneg k a b
  have e : gaugeWeight x * ((KBN.psiQ a : ℝ) + KBN.psiQ b) / 2 =
      -((cF k a b : ℝ) * ungaugedPair x) := by
    unfold gaugeWeight cF; rw [px]; push_cast
    have hne : (1 - (KBN.psiQ k : ℝ)) ≠ 0 := p1'.ne'
    field_simp
  rw [e]
  unfold wF
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

/-- The polynomial gauge term at the radii. -/
def gaugeTermF (p q k : ℕ) (r s d : ℝ) : ℝ :=
  (cF p q k : ℝ) * KBN.E1 (KBN.Ugen p) (r - 1) +
    ((cF q p k : ℝ) * KBN.E1 (KBN.Ugen q) (s - 1) + (cF k p q : ℝ) * KBN.E1 (KBN.Ugen k) (d - 1))

/-- The diagonal caps credit at the radii. -/
def diagCredit (p q k : ℕ) (r s d : ℝ) : ℝ :=
  (wF p q k : ℝ) * capsCorrection r r 1 + (wF q p k : ℝ) * capsCorrection s s 1 +
    (wF k p q : ℝ) * capsCorrection d d 1

/-- The gauge charge is bounded below by the diagonal caps credit minus the polynomial term. -/
lemma gaugeCharge_ge (hs : KBN.scalarCheck = true) (ha : KBN.gaugeAllOK = true) {p q k : ℕ}
    (hp : p < 7) (hq : q < 7) (hk : k < 7) {r s d : ℝ}
    (hr : RegionOwns p r) (hsr : RegionOwns q s) (hd : RegionOwns k d) :
    -gaugeTermF p q k r s d + diagCredit p q k r s d ≤ gaugeCharge r s d := by
  have ha' := ha
  simp only [KBN.gaugeAllOK, Bool.and_eq_true] at ha'
  have fac : ∀ m < 7, KBN.cellOK m = true := by
    intro m hm
    have h := List.all_eq_true.mp ha'.2 m (List.mem_range.mpr hm)
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have pr := KBN.gaugePsi_cell (fac p hp) (KBN.inCell_of_regionOwns hr)
  have ps := KBN.gaugePsi_cell (fac q hq) (KBN.inCell_of_regionOwns hsr)
  have pd := KBN.gaugePsi_cell (fac k hk) (KBN.inCell_of_regionOwns hd)
  have A := side_gauge (a := q) (b := k) hs ha hp hr
  have B := side_gauge (a := p) (b := k) hs ha hq hsr
  have C := side_gauge (a := p) (b := q) hs ha hk hd
  have e : gaugeCharge r s d = gaugeWeight r * ((KBN.psiQ q : ℝ) + KBN.psiQ k) / 2 +
      gaugeWeight s * ((KBN.psiQ p : ℝ) + KBN.psiQ k) / 2 +
      gaugeWeight d * ((KBN.psiQ p : ℝ) + KBN.psiQ q) / 2 := by
    unfold gaugeCharge; rw [pr, ps, pd]; ring
  rw [e]
  unfold gaugeTermF diagCredit
  linarith

/-- Caps correction with fixed pieces at the side cosines, plus the weighted diagonal caps. -/
def corrW (p q k : ℕ) (wr ws wd : ℚ) (r s d : ℝ) : ℝ :=
  capsCorrP p q r s (sideCos r s d) + capsCorrP p k r d (sideCos r d s) +
    capsCorrP q k s d (sideCos s d r) +
    ((wr : ℝ) * capsCorrP p p r r 1 + (ws : ℝ) * capsCorrP q q s s 1 + (wd : ℝ) * capsCorrP k k d d 1)

lemma corrW_nonneg (p q k : ℕ) {wr ws wd : ℚ} (hwr : (0:ℝ) ≤ wr) (hws : (0:ℝ) ≤ ws)
    (hwd : (0:ℝ) ≤ wd) (r s d : ℝ) : 0 ≤ corrW p q k wr ws wd r s d := by
  unfold corrW
  have := capsCorrP_nonneg p q r s (sideCos r s d)
  have := capsCorrP_nonneg p k r d (sideCos r d s)
  have := capsCorrP_nonneg q k s d (sideCos s d r)
  have := mul_nonneg hwr (capsCorrP_nonneg p p r r 1)
  have := mul_nonneg hws (capsCorrP_nonneg q q s s 1)
  have := mul_nonneg hwd (capsCorrP_nonneg k k d d 1)
  linarith

/-- Threshold soundness on every valid box. -/
lemma full_thr_soundW (p q k : ℕ) (u : Cap → Bool) (ap bp aq bq ak bk : ℚ) (wr ws wd : ℚ)
    (hwr : (0:ℝ) ≤ wr) (hws : (0:ℝ) ≤ ws) (hwd : (0:ℝ) ≤ wd)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) ≤ bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) ≤ bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (ka1 : 1 ≤ (ak:ℝ)) (kab : (ak:ℝ) ≤ bk) (kb7 : (bk:ℝ) ≤ 7/4)
    (B : Box) (hB : B.Valid) (x y z : ℝ) (hc : Cube x y z) :
    ((fullThrG (cdata u) ⟨⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),0⟩, wr, ws, wd⟩ B : ℚ) : ℝ) ≤
      (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) * ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y) *
        ((ak:ℝ) + ((bk:ℝ) - ak) * B.c.pt z))^18 *
      corrW p q k wr ws wd ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x)
        ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y) ((ak:ℝ) + ((bk:ℝ) - ak) * B.c.pt z) := by
  obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
  obtain ⟨ha, hb, hcc⟩ := hB
  obtain ⟨cr1, cr2, lr0, r1, r7⟩ := box_coord pa1 pab pb7 ha hx0 hx1
  obtain ⟨cs1, cs2, ls0, s1, s7⟩ := box_coord qa1 qab qb7 hb hy0 hy1
  obtain ⟨cd1, cd2, ld0, d1, d7⟩ := box_coord ka1 kab kb7 hcc hz0 hz1
  generalize (ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x = r' at *
  generalize (aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y = s' at *
  generalize (ak:ℝ) + ((bk:ℝ) - ak) * B.c.pt z = d' at *
  have t1 := cos_bounds lr0 ls0 ld0.le cr1 cr2 cs1 cs2 cd1 cd2
  have t2 := cos_bounds lr0 ld0 ls0.le cr1 cr2 cd1 cd2 cs1 cs2
  have t3 := cos_bounds ls0 ld0 lr0.le cs1 cs2 cd1 cd2 cr1 cr2
  have a1 := sideCos_abs r1 r7 s1 s7 d1 d7
  have a2 := sideCos_abs r1 r7 d1 d7 s1 s7
  have a3 := sideCos_abs s1 s7 d1 d7 r1 r7
  have k1 := capsLo_sound u p q cr1 cr2 cs1 cs2 t1.1 t1.2 a1.1 a1.2
  have k2 := capsLo_sound u p k cr1 cr2 cd1 cd2 t2.1 t2.2 a2.1 a2.2
  have k3 := capsLo_sound u q k cs1 cs2 cd1 cd2 t3.1 t3.2 a3.1 a3.2
  have one1 : ((1:ℚ):ℝ) ≤ (1:ℝ) := by norm_num
  have one2 : (1:ℝ) ≤ ((1:ℚ):ℝ) := by norm_num
  have j1 := mul_le_mul_of_nonneg_left
    (capsLo_sound u p p cr1 cr2 cr1 cr2 one1 one2 (by norm_num) le_rfl) hwr
  have j2 := mul_le_mul_of_nonneg_left
    (capsLo_sound u q q cs1 cs2 cs1 cs2 one1 one2 (by norm_num) le_rfl) hws
  have j3 := mul_le_mul_of_nonneg_left
    (capsLo_sound u k k cd1 cd2 cd1 cd2 one1 one2 (by norm_num) le_rfl) hwd
  set F : FullCaseG := ⟨⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),0⟩, wr, ws, wd⟩ with hF
  have hcorr : ((fullCorrLoG (cdata u) F B : ℚ) : ℝ) ≤ corrW p q k wr ws wd r' s' d' := by
    simp only [fullCorrLoG, fullCorrLo, diagCapsLo, hF, corrW]
    push_cast
    linarith
  have hcorr0 : ((max 0 (fullCorrLoG (cdata u) F B) : ℚ) : ℝ) ≤ corrW p q k wr ws wd r' s' d' := by
    push_cast
    exact max_le (corrW_nonneg p q k hwr hws hwd _ _ _) hcorr
  have hm0 : (0:ℝ) ≤ ((max 0 (fullCorrLoG (cdata u) F B) : ℚ) : ℝ) := by
    push_cast; exact le_max_left _ _
  have h2 : (0:ℝ) < coordLo (aq, bq) B.b := by exact_mod_cast ls0
  have h3 : (0:ℝ) < coordLo (ak, bk) B.c := by exact_mod_cast ld0
  have hfac : (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) * ((coordLo (aq, bq) B.b : ℚ) : ℝ) *
      ((coordLo (ak, bk) B.c : ℚ) : ℝ))^18 ≤ (2 * r' * s' * d')^18 := by
    have h1 : (0:ℝ) < coordLo (ap, bp) B.a := by exact_mod_cast lr0
    apply pow_le_pow_left₀ (by positivity)
    have e1 := mul_le_mul cr1 cs1 h2.le (by linarith)
    have e2 := mul_le_mul e1 cd1 h3.le (by positivity)
    nlinarith
  have hthr : ((fullThrG (cdata u) F B : ℚ) : ℝ) = (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) *
      ((coordLo (aq, bq) B.b : ℚ) : ℝ) * ((coordLo (ak, bk) B.c : ℚ) : ℝ))^18 *
      ((max 0 (fullCorrLoG (cdata u) F B) : ℚ) : ℝ) := by
    simp only [fullThrG, hF]; push_cast; ring
  rw [hthr]
  exact mul_le_mul hfac hcorr0 hm0 (pow_nonneg (by positivity) _)

theorem full_case_G_generic (hsc : KBN.scalarCheck = true) (hga : KBN.gaugeAllOK = true)
    (p q k : ℕ) (hp : p < 7) (hq : q < 7) (hk : k < 7) (u : Cap → Bool) (ap bp aq bq ak bk : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) < bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) < bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (ka1 : 1 ≤ (ak:ℝ)) (kab : (ak:ℝ) < bk) (kb7 : (bk:ℝ) ≤ 7/4)
    (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPolyAff (fullThrG (cdata u) ⟨⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),0⟩,
      wF p q k, wF q p k, wF k p q⟩) unit w fuel
      (fullPolyG p q k) (affOf (ap,bp)) (affOf (aq,bq)) (affOf (ak,bk)) = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : RegionOwns k d)
    (hrb : (ap:ℝ) ≤ r ∧ r ≤ bp) (hsb : (aq:ℝ) ≤ s ∧ s ≤ bq) (hdb : (ak:ℝ) ≤ d ∧ d ≤ bk) :
    sideCyclic r s d ≤ 0 := by
  have hwr := wF_nonneg p q k
  have hws := wF_nonneg q p k
  have hwd := wF_nonneg k p q
  let G : ℝ → ℝ → ℝ → ℝ := fun x y z =>
    (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * x) * ((aq:ℝ) + ((bq:ℝ) - aq) * y) *
      ((ak:ℝ) + ((bk:ℝ) - ak) * z))^18 *
    corrW p q k (wF p q k) (wF q p k) (wF k p q) ((ap:ℝ) + ((bp:ℝ) - ap) * x)
      ((aq:ℝ) + ((bq:ℝ) - aq) * y) ((ak:ℝ) + ((bk:ℝ) - ak) * z)
  have hG : ∀ x y z, Cube x y z → 0 ≤ G x y z := by
    intro x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    have e1 : (0:ℝ) ≤ ((bp:ℝ) - ap) * x := mul_nonneg (by linarith) hx0
    have e2 : (0:ℝ) ≤ ((bq:ℝ) - aq) * y := mul_nonneg (by linarith) hy0
    have e3 : (0:ℝ) ≤ ((bk:ℝ) - ak) * z := mul_nonneg (by linarith) hz0
    have f1 : (0:ℝ) ≤ (ap:ℝ) + ((bp:ℝ) - ap) * x := by linarith
    have f2 : (0:ℝ) ≤ (aq:ℝ) + ((bq:ℝ) - aq) * y := by linarith
    have f3 : (0:ℝ) ≤ (ak:ℝ) + ((bk:ℝ) - ak) * z := by linarith
    exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) f1) f2) f3) _)
      (corrW_nonneg p q k hwr hws hwd _ _ _)
  have hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((fullThrG (cdata u) ⟨⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),0⟩,
        wF p q k, wF q p k, wF k p q⟩ B : ℚ) : ℝ) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z) :=
    fun B hB x y z hc => full_thr_soundW p q k u ap bp aq bq ak bk _ _ _ hwr hws hwd
      pa1 pab.le pb7 qa1 qab.le qb7 ka1 kab.le kb7 B hB x y z hc
  have hsound := checkPolyAff_sound _ unit w _ _ _ _ _ G h hthr hG
  have hpx : (0:ℝ) < (bp:ℝ) - ap := by linarith
  have hpy : (0:ℝ) < (bq:ℝ) - aq := by linarith
  have hpz : (0:ℝ) < (bk:ℝ) - ak := by linarith
  set x := (r - ap)/((bp:ℝ) - ap)
  set y := (s - aq)/((bq:ℝ) - aq)
  set z := (d - ak)/((bk:ℝ) - ak)
  have hcube : Cube x y z := by
    refine ⟨div_nonneg (by linarith) hpx.le, ?_, div_nonneg (by linarith) hpy.le, ?_,
      div_nonneg (by linarith) hpz.le, ?_⟩
    · rw [div_le_one hpx]; linarith
    · rw [div_le_one hpy]; linarith
    · rw [div_le_one hpz]; linarith
  have hRx : (ap:ℝ) + ((bp:ℝ) - ap) * x = r := by simp only [x]; field_simp; ring
  have hSy : (aq:ℝ) + ((bq:ℝ) - aq) * y = s := by simp only [y]; field_simp; ring
  have hDz : (ak:ℝ) + ((bk:ℝ) - ak) * z = d := by simp only [z]; field_simp; ring
  have hb := hsound x y z hcube
  rw [affOf_eval, affOf_eval, affOf_eval] at hb
  simp only [G, hRx, hSy, hDz] at hb
  have r1 : 1 ≤ r := by linarith [hrb.1]
  have s1 : 1 ≤ s := by linarith [hsb.1]
  have d1 : 1 ≤ d := by linarith [hdb.1]
  have r7 : r ≤ 7/4 := by linarith [hrb.2]
  have s7 : s ≤ 7/4 := by linarith [hsb.2]
  have d7 : d ≤ 7/4 := by linarith [hdb.2]
  have he := CyclicPoly.eval_cyclic (CyclicPoly.coordinate 0) (CyclicPoly.coordinate 1)
    (CyclicPoly.coordinate 2) r s d
    (by simpa using r1) (by simpa using r7) (by simpa using s1) (by simpa using s7)
    (by simpa using d1) (by simpa using d7)
  have hpr := radial_piece_of_region hr
  have hps := radial_piece_of_region hs
  have hpd := radial_piece_of_region hd
  simp only [CyclicPoly.eval_coordinate0, CyclicPoly.eval_coordinate1, CyclicPoly.eval_coordinate2,
    hpr, hps, hpd] at he
  have hpolyU : CyclicPoly.eval (fullPolyU p q k) r s d =
      (2*r*s*d)^18 * polynomialSideCyclic r s d := by
    rw [fullPolyU, NPoly.cyclic_eq, NPoly.coordinate_eq]; exact he
  have hU := eval_p1F (KBN.Ugen p) r s d
  have hV := eval_p1F (KBN.Ugen q) r s d
  have hW := eval_p1F (KBN.Ugen k) r s d
  have hfac : CyclicPoly.eval factorF r s d = 2*r*s*d := by
    simp only [factorF, NPoly.scale_eq, NPoly.fastMul_eq, NPoly.coordinate_eq,
      CyclicPoly.eval_scale, CyclicPoly.eval_fastMul, CyclicPoly.eval_coordinate0,
      CyclicPoly.eval_coordinate1, CyclicPoly.eval_coordinate2]
    push_cast; ring
  have hpoly : CyclicPoly.eval (fullPolyG p q k) r s d =
      (2*r*s*d)^18 * (polynomialSideCyclic r s d + gaugeTermF p q k r s d) := by
    rw [fullPolyG, NPoly.fastAdd_eq, CyclicPoly.eval_fastAdd, hpolyU, gaugeF]
    simp only [NPoly.fastMul_eq, NPoly.fastPower_eq, NPoly.fastAdd_eq, NPoly.scale_eq,
      CyclicPoly.eval_fastMul, CyclicPoly.eval_fastPower, CyclicPoly.eval_fastAdd,
      CyclicPoly.eval_scale]
    rw [hfac, hU.1, hV.2.1, hW.2.2]
    unfold gaugeTermF
    ring
  rw [hpoly] at hb
  have hfpos : 0 < (2*r*s*d)^18 := by positivity
  have hle : polynomialSideCyclic r s d + gaugeTermF p q k r s d ≤
      corrW p q k (wF p q k) (wF q p k) (wF k p q) r s d :=
    le_of_mul_le_mul_left hb hfpos
  have c1 : capsCorrP p q r s (sideCos r s d) = capsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact capsCorrP_eq r1 r7 s1 s7 _
  have c2 : capsCorrP p k r d (sideCos r d s) = capsCorrection r d (sideCos r d s) := by
    rw [← hpr, ← hpd]; exact capsCorrP_eq r1 r7 d1 d7 _
  have c3 : capsCorrP q k s d (sideCos s d r) = capsCorrection s d (sideCos s d r) := by
    rw [← hps, ← hpd]; exact capsCorrP_eq s1 s7 d1 d7 _
  have c4 : capsCorrP p p r r 1 = capsCorrection r r 1 := by
    rw [← hpr]; exact capsCorrP_eq r1 r7 r1 r7 _
  have c5 : capsCorrP q q s s 1 = capsCorrection s s 1 := by
    rw [← hps]; exact capsCorrP_eq s1 s7 s1 s7 _
  have c6 : capsCorrP k k d d 1 = capsCorrection d d 1 := by
    rw [← hpd]; exact capsCorrP_eq d1 d7 d1 d7 _
  have g := gaugeCharge_ge hsc hga hp hq hk hr hs hd
  have o1 := otherCorr_nonneg r1 s1 r7 s7 (sideCos r s d)
  have o2 := otherCorr_nonneg r1 d1 r7 d7 (sideCos r d s)
  have o3 := otherCorr_nonneg s1 d1 s7 d7 (sideCos s d r)
  rw [sideCyclic_split]
  unfold corrW at hle
  rw [c1, c2, c3, c4, c5, c6] at hle
  unfold diagCredit at g
  linarith

theorem full_case_of_G (p q k : ℕ) (hp : p < 7) (hq : q < 7) (hk : k < 7) (u : Cap → Bool)
    (unit : ℚ) (fuel : ℕ) (h : fullCheckG u unit fuel p q k = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : RegionOwns k d) :
    sideCyclic r s d ≤ 0 := by
  obtain ⟨pa1, pab, pb7⟩ := breaks_range hp
  obtain ⟨qa1, qab, qb7⟩ := breaks_range hq
  obtain ⟨ka1, kab, kb7⟩ := breaks_range hk
  exact full_case_G_generic KBN.scalarCheck_true KBN.gaugeAllOK_true p q k hp hq hk u _ _ _ _ _ _
    pa1 pab pb7 qa1 qab qb7 ka1 kab kb7 unit _ fuel h
    hr hs hd (region_bounds hr) (region_bounds hs) (region_bounds hd)

/-- `CyclicSign V7.kernel` from the 84 full native checks and any proof of the exterior cases. -/
theorem cyclicSign_of_full_checksG (u : Cap → Bool) (unit : ℚ) (fuel : ℕ)
    (hfull : ∀ p ∈ fullCases, fullCheckG u unit fuel p.1 p.2.1 p.2.2 = true)
    (outside : ∀ p ∈ outsideCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.val s →
      r ≤ s → 7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) :
    CyclicSign kernel := by
  apply cyclicSign_of_112_cases _ outside
  intro p hp r s d hr hs hd _ _
  exact full_case_of_G p.1 p.2.1 p.2.2 p.1.isLt p.2.1.isLt p.2.2.isLt u unit fuel (hfull p hp)
    hr hs hd

end
end D4Bound.V7

#print axioms D4Bound.V7.full_case_of_G
#print axioms D4Bound.V7.cyclicSign_of_full_checksG
