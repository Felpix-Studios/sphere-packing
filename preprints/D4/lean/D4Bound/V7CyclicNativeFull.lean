import D4Bound.CyclicNativeCorrSound
import D4Bound.V7CyclicNativeLink
import D4Bound.V7PairMargin12
import D4Bound.V7CyclicCases
import D4Bound.V7PairSign

/-!
# Full cyclic cases from native checks

`full_case_of_check p q k u unit w fuel h`: a successful native check of the case
polynomial against the cap-and-gauge threshold proves `sideCyclic r s d ≤ 0`
for all radii owned by the regions `p, q, k`.
-/
namespace D4Bound.V7
open CyclicNative

noncomputable section

/-- The case polynomial on the unit cube. -/
def fullPoly (p q k : ℕ) : List ((ℕ × ℕ × ℕ) × ℚ) :=
  NPoly.cyclic NPoly.kdata p q k
    (NPoly.affine (breaks.getD p 0) (breaks.getD (p+1) 0) 0)
    (NPoly.affine (breaks.getD q 0) (breaks.getD (q+1) 0) 1)
    (NPoly.affine (breaks.getD k 0) (breaks.getD (k+1) 0) 2)

/-- The rawPair correction split. -/
lemma rawPair_split (r s t : ℝ) : rawPair r s t = polynomialPair r s t -
    (capsCorrection r s t + tentsCorrection r s t + allocationsCorrection r s t +
      graphsCorrection r s t) := by
  unfold rawPair polynomialPair; ring

def otherCorr (r s t : ℝ) : ℝ :=
  tentsCorrection r s t + allocationsCorrection r s t + graphsCorrection r s t

lemma otherCorr_nonneg {r s : ℝ} (hr1 : 1 ≤ r) (hs1 : 1 ≤ s) (hr : r ≤ 7/4) (hs : s ≤ 7/4) (t : ℝ) :
    0 ≤ otherCorr r s t := by
  unfold otherCorr
  have := tentsCorrection_nonneg hr1 hs1 hr hs t
  have := allocationsCorrection_nonneg hr1 hs1 hr hs t
  have := graphsCorrection_nonneg r s t
  linarith

def gaugeCharge (r s d : ℝ) : ℝ :=
  (gaugeWeight r*(gaugePsi s+gaugePsi d) + gaugeWeight s*(gaugePsi r+gaugePsi d) +
    gaugeWeight d*(gaugePsi r+gaugePsi s))/2

lemma sideCyclic_split (r s d : ℝ) : sideCyclic r s d = polynomialSideCyclic r s d -
    (capsCorrection r s (sideCos r s d) + capsCorrection r d (sideCos r d s) +
      capsCorrection s d (sideCos s d r) + otherCorr r s (sideCos r s d) +
      otherCorr r d (sideCos r d s) + otherCorr s d (sideCos s d r) + gaugeCharge r s d) := by
  rw [sideCyclic_gauge_identity]
  unfold rawSideCyclic polynomialSideCyclic gaugeCharge otherCorr
  rw [rawPair_split, rawPair_split, rawPair_split]
  ring

lemma gaugePsi_region {p : ℕ} {r : ℝ} (h : RegionOwns p r) :
    gaugePsi r = ((gaugePsiN p : ℚ) : ℝ) := by
  obtain ⟨hp, hl, hh⟩ := h
  unfold gaugePsi indicator gaugePsiN
  interval_cases p <;> norm_num [regionLo, regionHi, breaks, gaugeRadius, gaugeCount] at hl hh ⊢ <;>
    linarith

lemma gaugeWeight_region {p : ℕ} {r : ℝ} (h : RegionOwns p r) :
    ((gaugeLo p : ℚ) : ℝ) ≤ gaugeWeight r := by
  have h' := h
  obtain ⟨hp, hl, hh⟩ := h
  have hr1 : 1 ≤ r := by
    interval_cases p <;> norm_num [regionLo, breaks] at hl <;> linarith
  have hr7 : r ≤ 7/4 := by
    interval_cases p <;> norm_num [regionHi, breaks] at hh <;> linarith
  have hq := ungaugedPair_nonpos hr1 hr7
  have hpsi := gaugePsi_region h'
  interval_cases p
  · have hR : r ≤ 501473/500000 := by norm_num [regionHi, breaks] at hh; linarith
    have := ungaugedPair_first_margin hr1 hR
    rw [gaugeWeight_near (by linarith)]; norm_num [gaugeLo]; linarith
  · have := ungaugedPair_margin1 (r := r) (by norm_num [regionLo, breaks] at hl; linarith)
      (by norm_num [regionHi, breaks] at hh; linarith)
    rw [gaugeWeight_near (by norm_num [regionHi, breaks] at hh; linarith)]; norm_num [gaugeLo]; linarith
  · have := ungaugedPair_margin2 (r := r) (by norm_num [regionLo, breaks] at hl; linarith)
      (by norm_num [regionHi, breaks] at hh; linarith)
    rw [gaugeWeight_near (by norm_num [regionHi, breaks] at hh; linarith)]; norm_num [gaugeLo]; linarith
  all_goals (unfold gaugeWeight; rw [hpsi]; norm_num [gaugeLo, gaugePsiN]; linarith)

lemma gaugeConst_le {p q k : ℕ} {r s d : ℝ} (hp : RegionOwns p r) (hq : RegionOwns q s)
    (hk : RegionOwns k d) : ((gaugeConst p q k : ℚ) : ℝ) ≤ gaugeCharge r s d := by
  have a := gaugeWeight_region hp
  have b := gaugeWeight_region hq
  have c := gaugeWeight_region hk
  have pa := gaugePsi_region hp
  have pb := gaugePsi_region hq
  have pc := gaugePsi_region hk
  have nn : ∀ m, (0:ℝ) ≤ ((gaugePsiN m : ℚ) : ℝ) := by
    intro m; unfold gaugePsiN; split_ifs <;> norm_num
  have ng : ∀ m, (0:ℝ) ≤ ((gaugeLo m : ℚ) : ℝ) := by
    intro m; unfold gaugeLo; split_ifs <;> norm_num
  unfold gaugeConst gaugeCharge
  rw [pa, pb, pc]
  push_cast
  have := nn p; have := nn q; have := nn k
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have e1 := mul_le_mul_of_nonneg_right a (add_nonneg (nn q) (nn k))
  have e2 := mul_le_mul_of_nonneg_right b (add_nonneg (nn p) (nn k))
  have e3 := mul_le_mul_of_nonneg_right c (add_nonneg (nn p) (nn q))
  push_cast at e1 e2 e3
  linarith

lemma region_bounds {p : ℕ} {r : ℝ} (h : RegionOwns p r) :
    ((breaks.getD p 0 : ℚ) : ℝ) ≤ r ∧ r ≤ ((breaks.getD (p+1) 0 : ℚ) : ℝ) := by
  obtain ⟨hp, hl, hh⟩ := h
  refine ⟨?_, hh⟩
  split_ifs at hl
  · exact hl
  · exact hl.le

lemma breaks_range {p : ℕ} (hp : p < 7) :
    1 ≤ ((breaks.getD p 0 : ℚ) : ℝ) ∧ ((breaks.getD p 0 : ℚ) : ℝ) < ((breaks.getD (p+1) 0 : ℚ) : ℝ) ∧
      ((breaks.getD (p+1) 0 : ℚ) : ℝ) ≤ 7/4 := by
  interval_cases p <;> norm_num [breaks]

lemma box_coord {a b : ℚ} (ha : 1 ≤ (a:ℝ)) (hab : (a:ℝ) ≤ b) (hb7 : (b:ℝ) ≤ 7/4) {d : Dy}
    (hd : d.Valid) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((coordLo (a,b) d : ℚ) : ℝ) ≤ (a:ℝ) + ((b:ℝ) - a) * d.pt x ∧
    (a:ℝ) + ((b:ℝ) - a) * d.pt x ≤ ((coordHi (a,b) d : ℚ) : ℝ) ∧
    (0:ℚ) < coordLo (a,b) d ∧ 1 ≤ (a:ℝ) + ((b:ℝ) - a) * d.pt x ∧
    (a:ℝ) + ((b:ℝ) - a) * d.pt x ≤ 7/4 := by
  obtain ⟨u0, u1⟩ := Dy.pt_unit hd hx0 hx1
  obtain ⟨l, h⟩ := Dy.pt_mem d hx0 hx1
  have hlo : (0:ℝ) ≤ ((d.lo : ℚ) : ℝ) := by
    have : (0:ℚ) ≤ d.lo := by unfold Dy.lo; positivity
    exact_mod_cast this
  have hw : (0:ℝ) ≤ (b:ℝ) - a := by linarith
  have e1 := mul_le_mul_of_nonneg_left l hw
  have e2 := mul_le_mul_of_nonneg_left h hw
  have e3 := mul_nonneg hw hlo
  have e4 := mul_le_mul_of_nonneg_left u1 hw
  have e5 := mul_nonneg hw u0
  have cl : ((coordLo (a,b) d : ℚ) : ℝ) = (a:ℝ) + ((b:ℝ) - a) * ((d.lo : ℚ) : ℝ) := by
    simp only [coordLo]; push_cast; ring
  have ch : ((coordHi (a,b) d : ℚ) : ℝ) = (a:ℝ) + ((b:ℝ) - a) * ((d.hi : ℚ) : ℝ) := by
    simp only [coordHi]; push_cast; ring
  refine ⟨by rw [cl]; linarith, by rw [ch]; linarith, ?_, by linarith, by linarith⟩
  have : (0:ℝ) < ((coordLo (a,b) d : ℚ) : ℝ) := by rw [cl]; linarith
  exact_mod_cast this

/-- Pair-cap correction with fixed pieces, at side cosines, plus the gauge constant. -/
def corrP (p q k : ℕ) (r s d : ℝ) : ℝ :=
  capsCorrP p q r s (sideCos r s d) + capsCorrP p k r d (sideCos r d s) +
    capsCorrP q k s d (sideCos s d r) + ((gaugeConst p q k : ℚ) : ℝ)

lemma capsCorrP_nonneg (p q : ℕ) (r s t : ℝ) : 0 ≤ capsCorrP p q r s t := by
  unfold capsCorrP
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  have hv := caps_data_valid c hc
  apply div_nonneg _ (by norm_num)
  apply mul_nonneg (Rat.cast_nonneg.mpr hv.2.2.2.2.1)
  exact add_nonneg (mul_nonneg (le_max_left _ _) (capProbability_nonneg c r t))
    (mul_nonneg (le_max_left _ _) (capProbability_nonneg c s t))

lemma gaugeConst_nonneg (p q k : ℕ) : (0:ℝ) ≤ ((gaugeConst p q k : ℚ) : ℝ) := by
  have h : (0:ℚ) ≤ gaugeConst p q k := by
    unfold gaugeConst gaugeLo gaugePsiN
    split_ifs <;> norm_num
  exact_mod_cast h

lemma corrP_nonneg (p q k : ℕ) (r s d : ℝ) : 0 ≤ corrP p q k r s d := by
  unfold corrP
  have := capsCorrP_nonneg p q r s (sideCos r s d)
  have := capsCorrP_nonneg p k r d (sideCos r d s)
  have := capsCorrP_nonneg q k s d (sideCos s d r)
  have := gaugeConst_nonneg p q k
  linarith

/-- Threshold soundness on every valid box, for a generic full case. -/
lemma full_thr_sound (p q k : ℕ) (u : Cap → Bool) (ap bp aq bq ak bk : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) ≤ bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) ≤ bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (ka1 : 1 ≤ (ak:ℝ)) (kab : (ak:ℝ) ≤ bk) (kb7 : (bk:ℝ) ≤ 7/4)
    (B : Box) (hB : B.Valid) (x y z : ℝ) (hc : Cube x y z) :
    ((fullThr (cdata u) ⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),gaugeConst p q k⟩ B : ℚ) : ℝ) ≤
      (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) * ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y) *
        ((ak:ℝ) + ((bk:ℝ) - ak) * B.c.pt z))^18 *
      corrP p q k ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y)
        ((ak:ℝ) + ((bk:ℝ) - ak) * B.c.pt z) := by
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
  set F : FullCase := ⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),gaugeConst p q k⟩ with hF
  have hcorr : ((fullCorrLo (cdata u) F B : ℚ) : ℝ) ≤ corrP p q k r' s' d' := by
    simp only [fullCorrLo, hF, corrP]
    push_cast
    linarith
  have hcorr0 : ((max 0 (fullCorrLo (cdata u) F B) : ℚ) : ℝ) ≤ corrP p q k r' s' d' := by
    push_cast
    exact max_le (corrP_nonneg p q k _ _ _) hcorr
  have hm0 : (0:ℝ) ≤ ((max 0 (fullCorrLo (cdata u) F B) : ℚ) : ℝ) := by
    push_cast; exact le_max_left _ _
  have h1 : (0:ℝ) < coordLo (ap, bp) B.a := by exact_mod_cast lr0
  have h2 : (0:ℝ) < coordLo (aq, bq) B.b := by exact_mod_cast ls0
  have h3 : (0:ℝ) < coordLo (ak, bk) B.c := by exact_mod_cast ld0
  have hfac : (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) * ((coordLo (aq, bq) B.b : ℚ) : ℝ) *
      ((coordLo (ak, bk) B.c : ℚ) : ℝ))^18 ≤ (2 * r' * s' * d')^18 := by
    apply pow_le_pow_left₀ (by positivity)
    have e1 := mul_le_mul cr1 cs1 h2.le (by linarith)
    have e2 := mul_le_mul e1 cd1 h3.le (by positivity)
    nlinarith
  have hthr : ((fullThr (cdata u) F B : ℚ) : ℝ) = (2 * ((coordLo (ap, bp) B.a : ℚ) : ℝ) *
      ((coordLo (aq, bq) B.b : ℚ) : ℝ) * ((coordLo (ak, bk) B.c : ℚ) : ℝ))^18 *
      ((max 0 (fullCorrLo (cdata u) F B) : ℚ) : ℝ) := by
    simp only [fullThr, hF]; push_cast; ring
  rw [hthr]
  exact mul_le_mul hfac hcorr0 hm0 (pow_nonneg (by positivity) _)

/-- Generic full case: rational case intervals `[ap,bp]`, `[aq,bq]`, `[ak,bk]`. -/
theorem full_case_generic (p q k : ℕ) (u : Cap → Bool) (ap bp aq bq ak bk : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) < bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) < bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (ka1 : 1 ≤ (ak:ℝ)) (kab : (ak:ℝ) < bk) (kb7 : (bk:ℝ) ≤ 7/4)
    (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPoly (fullThr (cdata u) ⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),gaugeConst p q k⟩) unit w fuel
      (NPoly.cyclic NPoly.kdata p q k (NPoly.affine ap bp 0) (NPoly.affine aq bq 1)
        (NPoly.affine ak bk 2)) = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : RegionOwns k d)
    (hrb : (ap:ℝ) ≤ r ∧ r ≤ bp) (hsb : (aq:ℝ) ≤ s ∧ s ≤ bq) (hdb : (ak:ℝ) ≤ d ∧ d ≤ bk) :
    sideCyclic r s d ≤ 0 := by
  let G : ℝ → ℝ → ℝ → ℝ := fun x y z =>
    (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * x) * ((aq:ℝ) + ((bq:ℝ) - aq) * y) *
      ((ak:ℝ) + ((bk:ℝ) - ak) * z))^18 *
    corrP p q k ((ap:ℝ) + ((bp:ℝ) - ap) * x) ((aq:ℝ) + ((bq:ℝ) - aq) * y)
      ((ak:ℝ) + ((bk:ℝ) - ak) * z)
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
      (corrP_nonneg p q k _ _ _)
  have hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((fullThr (cdata u) ⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),gaugeConst p q k⟩ B : ℚ) : ℝ) ≤
        G (B.a.pt x) (B.b.pt y) (B.c.pt z) :=
    fun B hB x y z hc => full_thr_sound p q k u ap bp aq bq ak bk pa1 pab.le pb7 qa1 qab.le qb7
      ka1 kab.le kb7 B hB x y z hc
  have hsound := checkPoly_sound _ unit w _ _ G h hthr hG
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
  simp only [G, hRx, hSy, hDz] at hb
  have ea : CyclicPoly.eval (CyclicPoly.affine ap bp 0) x y z = r := by
    rw [CyclicPoly.eval_affine0]; exact hRx
  have eb : CyclicPoly.eval (CyclicPoly.affine aq bq 1) x y z = s := by
    rw [CyclicPoly.eval_affine1]; exact hSy
  have ec : CyclicPoly.eval (CyclicPoly.affine ak bk 2) x y z = d := by
    rw [CyclicPoly.eval_affine2]; exact hDz
  have r1 : 1 ≤ r := by linarith [hrb.1]
  have s1 : 1 ≤ s := by linarith [hsb.1]
  have d1 : 1 ≤ d := by linarith [hdb.1]
  have r7 : r ≤ 7/4 := by linarith [hrb.2]
  have s7 : s ≤ 7/4 := by linarith [hsb.2]
  have d7 : d ≤ 7/4 := by linarith [hdb.2]
  have he := CyclicPoly.eval_cyclic (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1)
    (CyclicPoly.affine ak bk 2) x y z
    (by rw [ea]; exact r1) (by rw [ea]; exact r7) (by rw [eb]; exact s1) (by rw [eb]; exact s7)
    (by rw [ec]; exact d1) (by rw [ec]; exact d7)
  have hpr := radial_piece_of_region hr
  have hps := radial_piece_of_region hs
  have hpd := radial_piece_of_region hd
  rw [ea, eb, ec, hpr, hps, hpd] at he
  have hpoly : CyclicPoly.eval (NPoly.cyclic NPoly.kdata p q k (NPoly.affine ap bp 0)
      (NPoly.affine aq bq 1) (NPoly.affine ak bk 2)) x y z =
      (2*r*s*d)^18 * polynomialSideCyclic r s d := by
    rw [NPoly.cyclic_eq, NPoly.affine_eq]; exact he
  rw [hpoly] at hb
  have hfpos : 0 < (2*r*s*d)^18 := by positivity
  have hle : polynomialSideCyclic r s d ≤ corrP p q k r s d := le_of_mul_le_mul_left hb hfpos
  have c1 : capsCorrP p q r s (sideCos r s d) = capsCorrection r s (sideCos r s d) := by
    rw [← hpr, ← hps]; exact capsCorrP_eq r1 r7 s1 s7 _
  have c2 : capsCorrP p k r d (sideCos r d s) = capsCorrection r d (sideCos r d s) := by
    rw [← hpr, ← hpd]; exact capsCorrP_eq r1 r7 d1 d7 _
  have c3 : capsCorrP q k s d (sideCos s d r) = capsCorrection s d (sideCos s d r) := by
    rw [← hps, ← hpd]; exact capsCorrP_eq s1 s7 d1 d7 _
  have g := gaugeConst_le hr hs hd
  have o1 := otherCorr_nonneg r1 s1 r7 s7 (sideCos r s d)
  have o2 := otherCorr_nonneg r1 d1 r7 d7 (sideCos r d s)
  have o3 := otherCorr_nonneg s1 d1 s7 d7 (sideCos s d r)
  rw [sideCyclic_split]
  unfold corrP at hle
  rw [c1, c2, c3] at hle
  linarith

theorem full_case_of_check (p q k : ℕ) (hp : p < 7) (hq : q < 7) (hk : k < 7) (u : Cap → Bool)
    (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPoly (fullThr (cdata u) (mkFull breaks p q k)) unit w fuel (fullPoly p q k) = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : RegionOwns k d) :
    sideCyclic r s d ≤ 0 := by
  obtain ⟨pa1, pab, pb7⟩ := breaks_range hp
  obtain ⟨qa1, qab, qb7⟩ := breaks_range hq
  obtain ⟨ka1, kab, kb7⟩ := breaks_range hk
  exact full_case_generic p q k u _ _ _ _ _ _ pa1 pab pb7 qa1 qab qb7 ka1 kab kb7 unit w fuel h
    hr hs hd (region_bounds hr) (region_bounds hs) (region_bounds hd)

end
end D4Bound.V7

#print axioms D4Bound.V7.full_case_of_check
