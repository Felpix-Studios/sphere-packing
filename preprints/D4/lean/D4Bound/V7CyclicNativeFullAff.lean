import D4Bound.V7CyclicNativeFull
import D4Bound.CyclicNativeShift

/-!
# Full cyclic cases from native checks of the unshifted polynomial

The polynomial is built in the original radii (cheap: the homogeneous factor `2rsd`
is one monomial); the affine maps to the case box are applied inside the checker.
-/
namespace D4Bound.V7
open CyclicNative

noncomputable section

/-- The unshifted case polynomial in `(r, s, d)`. -/
def fullPolyU (p q k : ℕ) : List ((ℕ × ℕ × ℕ) × ℚ) :=
  NPoly.cyclic NPoly.kdata p q k (NPoly.coordinate 0) (NPoly.coordinate 1) (NPoly.coordinate 2)

theorem full_case_aff_generic (p q k : ℕ) (u : Cap → Bool) (ap bp aq bq ak bk : ℚ)
    (pa1 : 1 ≤ (ap:ℝ)) (pab : (ap:ℝ) < bp) (pb7 : (bp:ℝ) ≤ 7/4)
    (qa1 : 1 ≤ (aq:ℝ)) (qab : (aq:ℝ) < bq) (qb7 : (bq:ℝ) ≤ 7/4)
    (ka1 : 1 ≤ (ak:ℝ)) (kab : (ak:ℝ) < bk) (kb7 : (bk:ℝ) ≤ 7/4)
    (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (h : checkPolyAff (fullThr (cdata u) ⟨p,q,k,(ap,bp),(aq,bq),(ak,bk),gaugeConst p q k⟩) unit w fuel
      (fullPolyU p q k) (affOf (ap,bp)) (affOf (aq,bq)) (affOf (ak,bk)) = true)
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
  have hpoly : CyclicPoly.eval (fullPolyU p q k) r s d = (2*r*s*d)^18 * polynomialSideCyclic r s d := by
    rw [fullPolyU, NPoly.cyclic_eq, NPoly.coordinate_eq]; exact he
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

/-- Native check of one full case, in terms of the region indices. -/
def fullCheckAff (u : Cap → Bool) (unit : ℚ) (fuel : ℕ) (p q k : ℕ) : Bool :=
  checkPolyAff (fullThr (cdata u) (mkFull breaks p q k)) unit (fullWidths (mkFull breaks p q k)) fuel
    (fullPolyU p q k) (affOf (breaks.getD p 0, breaks.getD (p+1) 0))
    (affOf (breaks.getD q 0, breaks.getD (q+1) 0)) (affOf (breaks.getD k 0, breaks.getD (k+1) 0))

theorem full_case_of_aff (p q k : ℕ) (hp : p < 7) (hq : q < 7) (hk : k < 7) (u : Cap → Bool)
    (unit : ℚ) (fuel : ℕ) (h : fullCheckAff u unit fuel p q k = true)
    {r s d : ℝ} (hr : RegionOwns p r) (hs : RegionOwns q s) (hd : RegionOwns k d) :
    sideCyclic r s d ≤ 0 := by
  obtain ⟨pa1, pab, pb7⟩ := breaks_range hp
  obtain ⟨qa1, qab, qb7⟩ := breaks_range hq
  obtain ⟨ka1, kab, kb7⟩ := breaks_range hk
  exact full_case_aff_generic p q k u _ _ _ _ _ _ pa1 pab pb7 qa1 qab qb7 ka1 kab kb7 unit _ fuel h
    hr hs hd (region_bounds hr) (region_bounds hs) (region_bounds hd)

/-- `CyclicSign V7.kernel` from the 84 full native checks and any proof of the exterior cases. -/
theorem cyclicSign_of_full_checks (u : Cap → Bool) (unit : ℚ) (fuel : ℕ)
    (hfull : ∀ p ∈ fullCases, fullCheckAff u unit fuel p.1 p.2.1 p.2.2 = true)
    (outside : ∀ p ∈ outsideCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.val s →
      r ≤ s → 7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) :
    CyclicSign kernel := by
  apply cyclicSign_of_112_cases _ outside
  intro p hp r s d hr hs hd _ _
  exact full_case_of_aff p.1 p.2.1 p.2.2 p.1.isLt p.2.1.isLt p.2.2.isLt u unit fuel (hfull p hp) hr hs hd

end
end D4Bound.V7

#print axioms D4Bound.V7.cyclicSign_of_full_checks
