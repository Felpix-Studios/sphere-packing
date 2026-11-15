import D4Bound.SphereMeasureSector

/-! Extend the nonnegative spherical-cap calculation to all closed tails. -/
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace D4Bound.SphereMeasure
noncomputable section
open Classical

def strictCap (v : R3) (a : ℝ) : Set UnitSphere := {u | a < ⟪(u : R3),v⟫}

theorem strictCap_measurable (v : R3) (a : ℝ) :
    MeasurableSet (strictCap v a) := by
  exact measurableSet_lt measurable_const
    (continuous_subtype_val.inner continuous_const).measurable

theorem uniformSphere_strictCap_of_nonneg
    (hpos : ∀ (v : R3), ‖v‖ = 1 → ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      uniformSphere.real (cap v a) = (1-a)/2)
    (v : R3) (hv : ‖v‖ = 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    uniformSphere.real (strictCap v a) = (1-a)/2 := by
  apply le_antisymm
  · calc
      uniformSphere.real (strictCap v a) ≤ uniformSphere.real (cap v a) :=
        measureReal_mono (by
          intro u hu
          change a < ⟪(u : R3),v⟫ at hu
          exact hu.le)
      _ = (1-a)/2 := hpos v hv a ha ha1
  · by_cases h1 : a = 1
    · rw [h1]
      simpa using (measureReal_nonneg : 0 ≤ uniformSphere.real (strictCap v 1))
    · have ha1' : a < 1 := lt_of_le_of_ne ha1 h1
      refine le_of_forall_pos_le_add fun ε hε => ?_
      let δ := min ε ((1-a)/2)
      have hd : 0 < δ := lt_min hε (by linarith)
      have hdε : δ ≤ ε := min_le_left _ _
      have hd1 : δ ≤ (1-a)/2 := min_le_right _ _
      have hb0 : 0 ≤ a+δ := by linarith
      have hb1 : a+δ ≤ 1 := by linarith
      have hsub : cap v (a+δ) ⊆ strictCap v a := by
        intro u hu
        change a+δ ≤ ⟪(u : R3),v⟫ at hu
        change a < ⟪(u : R3),v⟫
        linarith
      have hm := measureReal_mono (μ := uniformSphere) hsub
      rw [hpos v hv (a+δ) hb0 hb1] at hm
      linarith

/-- The cap formula at nonnegative levels determines every closed tail;
the strict-tail calculation explicitly handles boundaries of the caps. -/
theorem uniformSphere_cap_of_nonneg
    (hpos : ∀ (v : R3), ‖v‖ = 1 → ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      uniformSphere.real (cap v a) = (1-a)/2)
    (v : R3) (hv : ‖v‖ = 1) (a : ℝ) :
    uniformSphere.real (cap v a) = clip ((1-a)/2) := by
  by_cases hlo : a ≤ -1
  · have he : cap v a = univ := by
      apply Set.eq_univ_of_forall
      intro u
      have hu : ‖(u : R3)‖ = 1 := by
        simpa only [Metric.mem_sphere,dist_zero_right] using u.property
      exact hlo.trans (neg_one_le_real_inner_of_norm_eq_one hu hv)
    rw [he]
    simp only [probReal_univ]
    unfold clip
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  · by_cases hhi : 1 < a
    · have he : cap v a = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro u hu
        have hun : ‖(u : R3)‖ = 1 := by
          simpa only [Metric.mem_sphere,dist_zero_right] using u.property
        have hi := real_inner_le_one_of_norm_eq_one hun hv
        change a ≤ ⟪(u : R3),v⟫ at hu
        linarith
      rw [he]
      simp only [measureReal_empty]
      unfold clip
      rw [min_eq_right (by linarith),max_eq_left (by linarith)]
    · have ha0 : -1 < a := lt_of_not_ge hlo
      have ha1 : a ≤ 1 := le_of_not_gt hhi
      have hclip : clip ((1-a)/2) = (1-a)/2 := by
        unfold clip
        rw [min_eq_right (by linarith),max_eq_right (by linarith)]
      rw [hclip]
      by_cases ha : 0 ≤ a
      · exact hpos v hv a ha ha1
      · have hneg : a < 0 := lt_of_not_ge ha
        have he : cap v a = (strictCap (-v) (-a))ᶜ := by
          ext u
          simp only [cap,strictCap,mem_setOf_eq,mem_compl_iff,inner_neg_right,not_lt]
          constructor <;> intro h <;> linarith
        rw [he,measureReal_compl (strictCap_measurable (-v) (-a)),probReal_univ,
          uniformSphere_strictCap_of_nonneg hpos (-v) (by simpa using hv)
            (-a) (by linarith) (by linarith)]
        ring

end
end D4Bound.SphereMeasure

#print axioms D4Bound.SphereMeasure.uniformSphere_strictCap_of_nonneg
#print axioms D4Bound.SphereMeasure.uniformSphere_cap_of_nonneg
