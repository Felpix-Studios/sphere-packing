import D4Bound.V7PairSignBasic
import D4Bound.V7PairPolynomialData0
import D4Bound.V7PairPolynomialDataRest

/-! Closed-domain ungauged pair sign for the actual V7 kernel. -/
namespace D4Bound.V7
open PairPoly PairSignData
noncomputable section

private theorem pair_upper_sign0 {r : ℝ} (ha : (1 : ℝ) ≤ r) (hb : r ≤ ((501473/500000:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD0 r ≤ 0 := by
  exact pair_upper_sign_of_normalized 1 (501473/500000:ℚ) (by norm_num) pairD0
    negativeD0 negativeP0 negativeD0Den negativeP0Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (501473/500000:ℚ)-(1:ℚ)=(1473/500000:ℚ) := by norm_num
        simpa only [hw] using negativeD0_identity)
    (by have hw : (501473/500000:ℚ)-(1:ℚ)=(1473/500000:ℚ) := by norm_num
        simpa only [hw] using negativeP0_identity)
    negativeD0_positive negativeP0_positive (by simpa using ha) hb

private theorem pair_upper_sign1 {r : ℝ} (ha : ((501473/500000:ℚ) : ℝ) ≤ r) (hb : r ≤ ((1005643/1000000:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD1 r ≤ 0 := by
  exact pair_upper_sign_of_normalized (501473/500000:ℚ) (1005643/1000000:ℚ) (by norm_num) pairD1
    negativeD1 negativeP1 negativeD1Den negativeP1Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (1005643/1000000:ℚ)-(501473/500000:ℚ)=(2697/1000000:ℚ) := by norm_num
        simpa only [hw] using negativeD1_identity)
    (by have hw : (1005643/1000000:ℚ)-(501473/500000:ℚ)=(2697/1000000:ℚ) := by norm_num
        simpa only [hw] using negativeP1_identity)
    negativeD1_positive negativeP1_positive ha hb

private theorem pair_upper_sign2 {r : ℝ} (ha : ((1005643/1000000:ℚ) : ℝ) ≤ r) (hb : r ≤ ((50379/50000:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD2 r ≤ 0 := by
  exact pair_upper_sign_of_normalized (1005643/1000000:ℚ) (50379/50000:ℚ) (by norm_num) pairD2
    negativeD2 negativeP2 negativeD2Den negativeP2Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (50379/50000:ℚ)-(1005643/1000000:ℚ)=(1937/1000000:ℚ) := by norm_num
        simpa only [hw] using negativeD2_identity)
    (by have hw : (50379/50000:ℚ)-(1005643/1000000:ℚ)=(1937/1000000:ℚ) := by norm_num
        simpa only [hw] using negativeP2_identity)
    negativeD2_positive negativeP2_positive ha hb

private theorem pair_upper_sign3 {r : ℝ} (ha : ((50379/50000:ℚ) : ℝ) ≤ r) (hb : r ≤ ((50767/50000:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD3 r ≤ 0 := by
  exact pair_upper_sign_of_normalized (50379/50000:ℚ) (50767/50000:ℚ) (by norm_num) pairD3
    negativeD3 negativeP3 negativeD3Den negativeP3Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (50767/50000:ℚ)-(50379/50000:ℚ)=(97/12500:ℚ) := by norm_num
        simpa only [hw] using negativeD3_identity)
    (by have hw : (50767/50000:ℚ)-(50379/50000:ℚ)=(97/12500:ℚ) := by norm_num
        simpa only [hw] using negativeP3_identity)
    negativeD3_positive negativeP3_positive ha hb

private theorem pair_upper_sign4 {r : ℝ} (ha : ((50767/50000:ℚ) : ℝ) ≤ r) (hb : r ≤ ((102597/100000:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD4 r ≤ 0 := by
  exact pair_upper_sign_of_normalized (50767/50000:ℚ) (102597/100000:ℚ) (by norm_num) pairD4
    negativeD4 negativeP4 negativeD4Den negativeP4Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (102597/100000:ℚ)-(50767/50000:ℚ)=(1063/100000:ℚ) := by norm_num
        simpa only [hw] using negativeD4_identity)
    (by have hw : (102597/100000:ℚ)-(50767/50000:ℚ)=(1063/100000:ℚ) := by norm_num
        simpa only [hw] using negativeP4_identity)
    negativeD4_positive negativeP4_positive ha hb

private theorem pair_upper_sign5 {r : ℝ} (ha : ((102597/100000:ℚ) : ℝ) ≤ r) (hb : r ≤ ((3/2:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD5 r ≤ 0 := by
  exact pair_upper_sign_of_normalized (102597/100000:ℚ) (3/2:ℚ) (by norm_num) pairD5
    negativeD5 negativeP5 negativeD5Den negativeP5Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (3/2:ℚ)-(102597/100000:ℚ)=(47403/100000:ℚ) := by norm_num
        simpa only [hw] using negativeD5_identity)
    (by have hw : (3/2:ℚ)-(102597/100000:ℚ)=(47403/100000:ℚ) := by norm_num
        simpa only [hw] using negativeP5_identity)
    negativeD5_positive negativeP5_positive ha hb

private theorem pair_upper_sign6 {r : ℝ} (ha : ((3/2:ℚ) : ℝ) ≤ r) (hb : r ≤ ((7/4:ℚ) : ℝ)) :
    scalarRadius r + PairPoly.eval pairD6 r ≤ 0 := by
  exact pair_upper_sign_of_normalized (3/2:ℚ) (7/4:ℚ) (by norm_num) pairD6
    negativeD6 negativeP6 negativeD6Den negativeP6Den
    (by decide +kernel) (by decide +kernel)
    (by have hw : (7/4:ℚ)-(3/2:ℚ)=(1/4:ℚ) := by norm_num
        simpa only [hw] using negativeD6_identity)
    (by have hw : (7/4:ℚ)-(3/2:ℚ)=(1/4:ℚ) := by norm_num
        simpa only [hw] using negativeP6_identity)
    negativeD6_positive negativeP6_positive ha hb

/-- All actual component data, every radial endpoint, and the exponential term are included. -/
theorem ungaugedPair_nonpos {r : ℝ} (h1 : 1 ≤ r) (h7 : r ≤ 7/4) :
    ungaugedPair r ≤ 0 := by
  apply (ungaugedPair_le_upper h1 h7).trans
  rw [← PairPoly.eval_diagonal h1 h7]
  have hi := PairPoly.radialPiece_interval h1 h7
  have hn := radialPiece_lt_seven h7
  generalize hp : radialPiece r = p at *
  interval_cases p
  · rw [diagonal0_checked]
    apply pair_upper_sign0 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]
  · rw [diagonal1_checked]
    apply pair_upper_sign1 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]
  · rw [diagonal2_checked]
    apply pair_upper_sign2 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]
  · rw [diagonal3_checked]
    apply pair_upper_sign3 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]
  · rw [diagonal4_checked]
    apply pair_upper_sign4 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]
  · rw [diagonal5_checked]
    apply pair_upper_sign5 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]
  · rw [diagonal6_checked]
    apply pair_upper_sign6 <;> norm_num [breaks] at hi ⊢ <;> linarith [hi.1,hi.2]

/-- The actual gauge component is nonnegative on any supported admissible neighbourhood
with the checked third-radius count cap. No pair-sign hypothesis remains. -/
theorem gauge_energy_nonneg_proved (X : Finset E4) (hX : Admissible X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (hcount : countWithin X R3 ≤ 24) :
    0 ≤ gaugeEnergy X := by
  have hn : (0 : E4) ∉ X := by
    intro hz
    have h := hX.1 0 hz
    norm_num at h
  exact gauge_energy_nonneg X hn
    (fun x hx => ungaugedPair_nonpos (hX.1 x hx) (hR x hx)) hcount

#print axioms ungaugedPair_nonpos
#print axioms gauge_energy_nonneg_proved
end
end D4Bound.V7
