import D4Bound.V7CyclicOutsideExtW

/-!
# Exterior cyclic cases on sub-boxes

`extCheckWS u unit fuel p q ap bp aq bq` is `extCheckW` on the sub-box `[ap,bp] × [aq,bq]` of the
case `(p,q)` (the radial pieces stay `p`, `q`). `extWS_case_of_check` gives the `outside`
obligation for radii in the sub-box. Sub-boxes let one case use a different unit on each part,
which keeps the integer coefficients small (Lean boxes integers below about 2^31) while keeping
enough precision where `(2rs)^18` is small.
-/

namespace D4Bound.V7
open CyclicNative

/-- Range conditions of a sub-box (checked by `decide` on rationals). -/
def extSubOK (ap bp aq bq : ℚ) : Bool :=
  decide (1 ≤ ap) && decide (ap < bp) && decide (bp ≤ 7/4) &&
    decide (1 ≤ aq) && decide (aq < bq) && decide (bq ≤ 7/4)

/-- Native check of the sub-box `[ap,bp] × [aq,bq]` of exterior case `(p,q)`. -/
def extCheckWS (u : Cap → Bool) (unit : ℚ) (fuel : ℕ) (p q : ℕ) (ap bp aq bq : ℚ) : Bool :=
  checkPolyAff (extThrW (cdata u) xdata ⟨⟨p, q, (ap, bp), (aq, bq), 0⟩, wX p q, wX q p⟩) unit
    (bp - ap, bq - aq, 1) fuel (extPolyG p q) (affOf (ap, bp)) (affOf (aq, bq)) (affOf (0, 1))

noncomputable section

theorem extWS_case_of_check (hsc : KBN.scalarCheck = true) (hga : KBN.gaugeAllOK = true)
    (p q : ℕ) (hp : p < 7) (hq : q < 7) (u : Cap → Bool) (unit : ℚ) (fuel : ℕ)
    (ap bp aq bq : ℚ) (hab : extSubOK ap bp aq bq = true)
    (h : extCheckWS u unit fuel p q ap bp aq bq = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s)
    (hrb : (ap:ℝ) ≤ r ∧ r ≤ bp) (hsb : (aq:ℝ) ≤ s ∧ s ≤ bq)
    (hd : 7/4 < d) (htri : d ≤ r+s) :
    pair r s (sideCos r s d) ≤ 0 := by
  have hwr := wX_nonneg p q
  have hws := wX_nonneg q p
  simp only [extSubOK, Bool.and_eq_true, decide_eq_true_eq] at hab
  obtain ⟨⟨⟨⟨⟨pa1', pab'⟩, pb7'⟩, qa1'⟩, qab'⟩, qb7'⟩ := hab
  have pa1 : (1:ℝ) ≤ ap := by exact_mod_cast pa1'
  have pab : (ap:ℝ) < bp := by exact_mod_cast pab'
  have pb7 : (bp:ℝ) ≤ 7/4 := by
    have : ((bp:ℚ):ℝ) ≤ ((7/4:ℚ):ℝ) := by exact_mod_cast pb7'
    simpa using this
  have qa1 : (1:ℝ) ≤ aq := by exact_mod_cast qa1'
  have qab : (aq:ℝ) < bq := by exact_mod_cast qab'
  have qb7 : (bq:ℝ) ≤ 7/4 := by
    have : ((bq:ℚ):ℝ) ≤ ((7/4:ℚ):ℝ) := by exact_mod_cast qb7'
    simpa using this
  unfold extCheckWS at h
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

#print axioms D4Bound.V7.extWS_case_of_check
