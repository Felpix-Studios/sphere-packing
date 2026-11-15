import D4Bound.CyclicNativeExtSound
import D4Bound.V7CyclicNativeFull

/-!
# Exterior cyclic cases from native checks

`ext_case_of_check p q u unit w fuel h`: a successful native check proves
`pair r s (sideCos r s d) ≤ 0` for radii owned by regions `p, q` and every
`7/4 < d ≤ r+s`. Coordinates `(r, s, z)`, `t = -1 + z((r+s)^2-49/16)/(2rs)`.
-/
namespace D4Bound.V7
open CyclicNative

noncomputable section

def xdata : XData := ⟨tents.map toTentN, graphs.map toGraphN, allocations.map toAllocN⟩

def extPolyOf (ap bp aq bq : ℚ) (p q : ℕ) : List ((ℕ × ℕ × ℕ) × ℚ) :=
  NPoly.pair NPoly.kdata p q (NPoly.affine ap bp 0) (NPoly.affine aq bq 1)
    (extA (NPoly.affine ap bp 0) (NPoly.affine aq bq 1)) (extB (NPoly.affine ap bp 0) (NPoly.affine aq bq 1))

def extPoly (p q : ℕ) : List ((ℕ × ℕ × ℕ) × ℚ) :=
  extPolyOf (breaks.getD p 0) (breaks.getD (p+1) 0) (breaks.getD q 0) (breaks.getD (q+1) 0) p q

lemma eval_extB (a b : NPoly.Poly) (x y z : ℝ) :
    CyclicPoly.eval (extB a b) x y z = 2 * CyclicPoly.eval a x y z * CyclicPoly.eval b x y z := by
  simp only [extB, NPoly.scale_eq, NPoly.fastMul_eq, CyclicPoly.eval_scale, CyclicPoly.eval_fastMul]
  push_cast; ring

lemma eval_extA (a b : NPoly.Poly) (x y z : ℝ) :
    CyclicPoly.eval (extA a b) x y z = -(2 * CyclicPoly.eval a x y z * CyclicPoly.eval b x y z) +
      z * ((CyclicPoly.eval a x y z + CyclicPoly.eval b x y z)^2 - 49/16) := by
  have hB := eval_extB a b x y z
  simp only [extA, NPoly.scale_eq, NPoly.fastMul_eq, NPoly.fastAdd_eq, NPoly.fastPower_eq,
    NPoly.coordinate_eq, NPoly.constant_eq, CyclicPoly.eval_scale, CyclicPoly.eval_fastMul,
    CyclicPoly.eval_fastAdd, CyclicPoly.eval_fastPower, CyclicPoly.eval_coordinate2,
    CyclicPoly.eval_constant] at hB ⊢
  rw [hB]; push_cast; ring

lemma pair_split (r s t : ℝ) : pair r s t = polynomialPair r s t -
    (capsCorrection r s t + otherCorr r s t +
      (gaugeWeight r*gaugePsi s + gaugeWeight s*gaugePsi r)/2) := by
  unfold pair otherCorr; rw [rawPair_split]; ring

lemma gaugeConstExt_le {p q : ℕ} {r s : ℝ} (hp : RegionOwns p r) (hq : RegionOwns q s) :
    ((gaugeConstExt p q : ℚ) : ℝ) ≤ (gaugeWeight r*gaugePsi s + gaugeWeight s*gaugePsi r)/2 := by
  have a := gaugeWeight_region hp
  have b := gaugeWeight_region hq
  have pa := gaugePsi_region hp
  have pb := gaugePsi_region hq
  have nn : ∀ m, (0:ℝ) ≤ ((gaugePsiN m : ℚ) : ℝ) := by
    intro m; unfold gaugePsiN; split_ifs <;> norm_num
  unfold gaugeConstExt
  rw [pa, pb]
  push_cast
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have e1 := mul_le_mul_of_nonneg_right a (nn q)
  have e2 := mul_le_mul_of_nonneg_right b (nn p)
  push_cast at e1 e2
  linarith

def corrX (p q : ℕ) (r s z : ℝ) : ℝ :=
  capsCorrP p q r s (extT r s z) + tentsCorrP p q r s (extT r s z) +
    graphsCorrection r s (extT r s z) + allocsCorrP p q r s (extT r s z) +
    ((gaugeConstExt p q : ℚ) : ℝ)

lemma corrX_nonneg (p q : ℕ) (r s z : ℝ) : 0 ≤ corrX p q r s z := by
  unfold corrX
  have := capsCorrP_nonneg p q r s (extT r s z)
  have := tentsCorrP_nonneg p q r s (extT r s z)
  have := graphsCorrection_nonneg r s (extT r s z)
  have := allocsCorrP_nonneg p q r s (extT r s z)
  have : (0:ℝ) ≤ ((gaugeConstExt p q : ℚ) : ℝ) := by
    have h : (0:ℚ) ≤ gaugeConstExt p q := by
      unfold gaugeConstExt gaugeLo gaugePsiN; split_ifs <;> norm_num
    exact_mod_cast h
  linarith

lemma ext_thr_sound (p q : ℕ) (u : Cap → Bool) (ap bp aq bq : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) ≤ bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) ≤ bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (B : Box) (hB : B.Valid) (x y z : ℝ) (hc : Cube x y z) :
    ((extThr (cdata u) xdata ⟨p,q,(ap,bp),(aq,bq),gaugeConstExt p q⟩ B : ℚ) : ℝ) ≤
      (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) * ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y))^18 *
      corrX p q ((ap:ℝ) + ((bp:ℝ) - ap) * B.a.pt x) ((aq:ℝ) + ((bq:ℝ) - aq) * B.b.pt y) (B.c.pt z) := by
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
  set E : ExtCase := ⟨p,q,(ap,bp),(aq,bq),gaugeConstExt p q⟩ with hE
  have hcorr : ((extCorrLo (cdata u) xdata E B : ℚ) : ℝ) ≤ corrX p q r' s' z' := by
    simp only [cdata] at k1
    simp only [extCorrLo, hE, xdata, cdata, Rat.cast_add]
    unfold corrX
    linarith
  have hcorr0 : ((max 0 (extCorrLo (cdata u) xdata E B) : ℚ) : ℝ) ≤ corrX p q r' s' z' := by
    push_cast
    exact max_le (corrX_nonneg p q _ _ _) hcorr
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

theorem ext_case_generic (p q : ℕ) (u : Cap → Bool) (ap bp aq bq : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) < bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) < bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPoly (extThr (cdata u) xdata ⟨p,q,(ap,bp),(aq,bq),gaugeConstExt p q⟩) unit w fuel
      (extPolyOf ap bp aq bq p q) = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s)
    (hrb : (ap:ℝ) ≤ r ∧ r ≤ bp) (hsb : (aq:ℝ) ≤ s ∧ s ≤ bq) (hd : 7/4 < d) (htri : d ≤ r+s) :
    pair r s (sideCos r s d) ≤ 0 := by
  let G : ℝ → ℝ → ℝ → ℝ := fun x y z =>
    (2 * ((ap:ℝ) + ((bp:ℝ) - ap) * x) * ((aq:ℝ) + ((bq:ℝ) - aq) * y))^18 *
    corrX p q ((ap:ℝ) + ((bp:ℝ) - ap) * x) ((aq:ℝ) + ((bq:ℝ) - aq) * y) z
  have hG : ∀ x y z, Cube x y z → 0 ≤ G x y z := by
    intro x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    have e1 : (0:ℝ) ≤ ((bp:ℝ) - ap) * x := mul_nonneg (by linarith) hx0
    have e2 : (0:ℝ) ≤ ((bq:ℝ) - aq) * y := mul_nonneg (by linarith) hy0
    have f1 : (0:ℝ) ≤ (ap:ℝ) + ((bp:ℝ) - ap) * x := by linarith
    have f2 : (0:ℝ) ≤ (aq:ℝ) + ((bq:ℝ) - aq) * y := by linarith
    exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) f1) f2) _) (corrX_nonneg p q _ _ _)
  have hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((extThr (cdata u) xdata ⟨p,q,(ap,bp),(aq,bq),gaugeConstExt p q⟩ B : ℚ) : ℝ) ≤
        G (B.a.pt x) (B.b.pt y) (B.c.pt z) :=
    fun B hB x y z hc => ext_thr_sound p q u ap bp aq bq pa1 pab.le pb7 qa1 qab.le qb7 B hB x y z hc
  have hsound := checkPoly_sound _ unit w _ _ G h hthr hG
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
  simp only [G, hRx, hSy] at hb
  have ea : CyclicPoly.eval (CyclicPoly.affine ap bp 0) x y z = r := by
    rw [CyclicPoly.eval_affine0]; exact hRx
  have eb : CyclicPoly.eval (CyclicPoly.affine aq bq 1) x y z = s := by
    rw [CyclicPoly.eval_affine1]; exact hSy
  have eA := eval_extA (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1) x y z
  have eB := eval_extB (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1) x y z
  rw [ea, eb] at eA eB
  have hBne : CyclicPoly.eval (extB (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1)) x y z ≠ 0 := by
    rw [eB]; positivity
  have he := CyclicPoly.eval_pair (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1)
    (extA (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1))
    (extB (CyclicPoly.affine ap bp 0) (CyclicPoly.affine aq bq 1))
    x y z (by rw [ea]; exact r1) (by rw [ea]; exact r7) (by rw [eb]; exact s1) (by rw [eb]; exact s7) hBne
  rw [ea, eb, radial_piece_of_region hr, radial_piece_of_region hs, eA, eB] at he
  have ht : (-(2*r*s) + z*((r+s)^2 - 49/16)) / (2*r*s) = sideCos r s d := by
    unfold sideCos; rw [hzt]; field_simp; ring
  rw [ht] at he
  have hpoly : CyclicPoly.eval (extPolyOf ap bp aq bq p q) x y z =
      (2*r*s)^18 * polynomialPair r s (sideCos r s d) := by
    rw [extPolyOf, NPoly.pair_eq, NPoly.affine_eq]
    exact he
  rw [hpoly] at hb
  have hfpos : 0 < (2*r*s)^18 := by positivity
  have hle : polynomialPair r s (sideCos r s d) ≤ corrX p q r s z := le_of_mul_le_mul_left hb hfpos
  have hT : extT r s z = sideCos r s d := by unfold extT sideCos; rw [hzt]; ring
  unfold corrX at hle
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
  have g := gaugeConstExt_le hr hs
  rw [pair_split]
  unfold otherCorr
  linarith

theorem ext_case_of_check (p q : ℕ) (hp : p < 7) (hq : q < 7) (u : Cap → Bool)
    (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPoly (extThr (cdata u) xdata (mkExt breaks p q)) unit w fuel (extPoly p q) = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : 7/4 < d) (htri : d ≤ r+s) :
    pair r s (sideCos r s d) ≤ 0 := by
  obtain ⟨pa1, pab, pb7⟩ := breaks_range hp
  obtain ⟨qa1, qab, qb7⟩ := breaks_range hq
  exact ext_case_generic p q u _ _ _ _ pa1 pab pb7 qa1 qab qb7 unit w fuel h hr hs
    (region_bounds hr) (region_bounds hs) hd htri

end
end D4Bound.V7

#print axioms D4Bound.V7.ext_case_of_check
