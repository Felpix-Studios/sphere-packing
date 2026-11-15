import D4Bound.V7CyclicGauge
import D4Bound.V7PairUpper

/-! The actual polynomial part dominates the raw cyclic expression because
all four discarded correction families are nonnegative. -/
namespace D4Bound.V7
noncomputable section

def polynomialPair (r s t : ℝ) : ℝ :=
  gramPair r s t + sphericalPair r s t + conditionalPair r s +
    (countPolynomials.map fun c => countPair c r s).sum

def polynomialSideCyclic (r s d : ℝ) : ℝ :=
  polynomialPair r s (sideCos r s d) + polynomialPair r d (sideCos r d s) +
    polynomialPair s d (sideCos s d r)

theorem rawPair_le_polynomialPair {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hR : r ≤ 7/4) (hS : s ≤ 7/4) (t : ℝ) :
    rawPair r s t ≤ polynomialPair r s t := by
  have hc := capsCorrection_nonneg hr hs hR hS t
  have ht := tentsCorrection_nonneg hr hs hR hS t
  have ha := allocationsCorrection_nonneg hr hs hR hS t
  have hg := graphsCorrection_nonneg r s t
  unfold rawPair polynomialPair
  linarith

theorem rawSideCyclic_le_polynomialSideCyclic {r s d : ℝ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hd : 1 ≤ d)
    (hR : r ≤ 7/4) (hS : s ≤ 7/4) (hD : d ≤ 7/4) :
    rawSideCyclic r s d ≤ polynomialSideCyclic r s d := by
  exact add_le_add (add_le_add
    (rawPair_le_polynomialPair hr hs hR hS _)
    (rawPair_le_polynomialPair hr hd hR hD _))
    (rawPair_le_polynomialPair hs hd hS hD _)

/-- This leaf interface needs only the polynomial upper and quantitative radial
majorant. No cap probability lower witnesses are needed for the first near leaf. -/
theorem sideCyclic_near_nonpos_of_polynomial {r s d u c : ℝ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hd : 1 ≤ d)
    (hR : r ≤ 50379/50000) (hS : s ≤ 50379/50000) (hD : d ≤ 50379/50000)
    (hpoly : polynomialSideCyclic r s d ≤ u)
    (hqr : ungaugedPair r ≤ -c) (hqs : ungaugedPair s ≤ -c)
    (hqd : ungaugedPair d ≤ -c) (hpay : 23*u ≤ 3*c) : sideCyclic r s d ≤ 0 := by
  exact sideCyclic_near_nonpos hR hS hD
    ((rawSideCyclic_le_polynomialSideCyclic hr hs hd (by linarith) (by linarith)
      (by linarith)).trans hpoly) hqr hqs hqd hpay

#print axioms rawSideCyclic_le_polynomialSideCyclic
#print axioms sideCyclic_near_nonpos_of_polynomial
end
end D4Bound.V7
