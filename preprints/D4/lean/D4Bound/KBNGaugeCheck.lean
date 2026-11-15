import D4Bound.KBNGaugeTabSound
import D4Bound.KernelBoxNativeCheckScalar

/-! `native_decide` component: the gauge tables and the scalar segment checks on cells 5-6. -/

namespace D4Bound.KBN

theorem gaugeAllOK_true : gaugeAllOK = true := by native_decide

/-- Gauge-weight lower bound on a dyadic box of region `k`, with no hypotheses left except
the box membership. -/
theorem gaugeLoDy_le {k num lev : ℕ} (hk : k < 7) {r : ℝ} (hr : V7.RegionOwns k r)
    (h1 : ((V7.breaks.getD k 0 + (V7.breaks.getD (k + 1) 0 - V7.breaks.getD k 0) *
      ((num : ℚ) / (2 ^ lev : ℕ)) : ℚ) : ℝ) ≤ r)
    (h2 : r ≤ ((V7.breaks.getD k 0 + (V7.breaks.getD (k + 1) 0 - V7.breaks.getD k 0) *
      (((num + 1 : ℕ) : ℚ) / (2 ^ lev : ℕ)) : ℚ) : ℝ)) :
    (GaugeTab.gaugeLoDy (GaugeTab.gaugeTab k) (GaugeTab.gaugeDepth k) num lev : ℝ) ≤
      V7.gaugeWeight r :=
  gaugeLoDy_sound scalarCheck_true gaugeAllOK_true hk hr h1 h2

end D4Bound.KBN

#print axioms D4Bound.KBN.gaugeLoDy_sound
#print axioms D4Bound.KBN.gaugeLoDy_le
