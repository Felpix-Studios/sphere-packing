import D4Bound.V7CyclicGeometry

/-! Exact quantitative gauge identities used by cyclic leaf certificates.
These lemmas expose the actual remaining sign obligations; they do not assume
a Python lower bound or promote the full cyclic inequality to a theorem. -/
namespace D4Bound.V7
noncomputable section

def rawSideCyclic (r s d : ℝ) : ℝ :=
  rawPair r s (sideCos r s d) + rawPair r d (sideCos r d s) +
    rawPair s d (sideCos s d r)

/-- Three pair-gauge charges combine to a weighted sum of the three radial weights. -/
theorem sideCyclic_gauge_identity (r s d : ℝ) :
    sideCyclic r s d = rawSideCyclic r s d -
      (gaugeWeight r*(gaugePsi s+gaugePsi d) +
       gaugeWeight s*(gaugePsi r+gaugePsi d) +
       gaugeWeight d*(gaugePsi r+gaugePsi s))/2 := by
  unfold sideCyclic rawSideCyclic pair
  ring

theorem gaugePsi_near {r : ℝ} (hr : r ≤ 50379/50000) : gaugePsi r = 1/24 := by
  norm_num [gaugePsi,indicator,gaugeRadius,gaugeCount,hr]

/-- On the near shell the exact gauge multiplier is `24/23`. -/
theorem gaugeWeight_near {r : ℝ} (hr : r ≤ 50379/50000) :
    gaugeWeight r = -(24/23)*ungaugedPair r := by
  rw [gaugeWeight,gaugePsi_near hr]
  ring

theorem sideCyclic_gauge_near {r s d : ℝ}
    (hr : r ≤ 50379/50000) (hs : s ≤ 50379/50000) (hd : d ≤ 50379/50000) :
    sideCyclic r s d = rawSideCyclic r s d +
      (ungaugedPair r+ungaugedPair s+ungaugedPair d)/23 := by
  rw [sideCyclic_gauge_identity,gaugePsi_near hr,gaugePsi_near hs,gaugePsi_near hd,
    gaugeWeight_near hr,gaugeWeight_near hs,gaugeWeight_near hd]
  ring

/-- A quantitative radial pair majorant and raw cyclic upper bound suffice
on a near-shell leaf. The actual two functions, not opaque proof flags, occur. -/
theorem sideCyclic_near_nonpos {r s d u c : ℝ}
    (hr : r ≤ 50379/50000) (hs : s ≤ 50379/50000) (hd : d ≤ 50379/50000)
    (hraw : rawSideCyclic r s d ≤ u)
    (hqr : ungaugedPair r ≤ -c) (hqs : ungaugedPair s ≤ -c)
    (hqd : ungaugedPair d ≤ -c) (hpay : 23*u ≤ 3*c) :
    sideCyclic r s d ≤ 0 := by
  rw [sideCyclic_gauge_near hr hs hd]
  linarith

#print axioms sideCyclic_gauge_identity
#print axioms sideCyclic_gauge_near
#print axioms sideCyclic_near_nonpos
end
end D4Bound.V7
