import D4Bound.SphereMeasure

/-! Disk-slice calculation of the volume of a three-dimensional conical sector. -/
open MeasureTheory Set
open scoped ENNReal
namespace D4Bound.SphereMeasure
noncomputable section
open Classical

abbrev R2 := EuclideanSpace ℝ (Fin 2)

def diskSolid (l u : ℝ) (f : ℝ → ℝ) : Set (ℝ × R2) :=
  {p | p.1 ∈ Icc l u ∧ p.2 ∈ Metric.closedBall 0 (Real.sqrt (f p.1))}

theorem diskSolid_measurable (l u : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    MeasurableSet (diskSolid l u f) := by
  have h1 : MeasurableSet {p : ℝ × R2 | p.1 ∈ Icc l u} :=
    measurable_fst measurableSet_Icc
  have h2 : MeasurableSet {p : ℝ × R2 | ‖p.2‖ ≤ Real.sqrt (f p.1)} :=
    measurableSet_le (measurable_snd.norm) ((hf.measurable.comp measurable_fst).sqrt)
  simpa only [diskSolid,Metric.mem_closedBall,dist_zero_right,Set.setOf_and] using h1.inter h2

/-- Cavalieri/Fubini for a solid with circular slices of squared radius `f`. -/
theorem volume_diskSolid (l u : ℝ) (hlu : l ≤ u) (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ z ∈ Icc l u, 0 ≤ f z) :
    volume (diskSolid l u f) = ENNReal.ofReal (Real.pi * ∫ z in l..u, f z) := by
  have hslice (z : ℝ) : Prod.mk z ⁻¹' diskSolid l u f =
      if z ∈ Icc l u then Metric.closedBall (0 : R2) (Real.sqrt (f z)) else ∅ := by
    ext w
    by_cases h : z ∈ Icc l u <;>
      simp only [diskSolid,Set.mem_preimage,Set.mem_setOf_eq,h,if_true,if_false,
        true_and,false_and,Set.mem_empty_iff_false]
  calc
    volume (diskSolid l u f) =
        ∫⁻ z : ℝ, volume (Prod.mk z ⁻¹' diskSolid l u f) :=
      Measure.prod_apply (diskSolid_measurable l u f hf)
    _ = ∫⁻ z : ℝ, (Icc l u).indicator (fun z => ENNReal.ofReal (Real.pi * f z)) z := by
      apply lintegral_congr
      intro z
      rw [hslice z]
      by_cases hz : z ∈ Icc l u
      · rw [if_pos hz,Set.indicator_of_mem hz,EuclideanSpace.volume_closedBall_fin_two,
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,Real.sq_sqrt (hn z hz),
          ← ENNReal.ofReal_mul (hn z hz)]
        rw [mul_comm]
      · simp [hz]
    _ = ENNReal.ofReal (∫ z in Icc l u, Real.pi * f z) := by
      rw [lintegral_indicator measurableSet_Icc]
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact (hf.const_mul Real.pi).continuousOn.integrableOn_Icc
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
        exact mul_nonneg Real.pi_pos.le (hn z hz)
    _ = ENNReal.ofReal (Real.pi * ∫ z in l..u, f z) := by
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hlu]

theorem volume_cone_lower {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    volume (diskSolid 0 a (fun z => (1-a^2)/a^2*z^2)) =
      ENNReal.ofReal (Real.pi * ((1-a^2)*a/3)) := by
  rw [volume_diskSolid 0 a ha.le _ (by fun_prop)]
  · congr 1
    rw [intervalIntegral.integral_const_mul,integral_pow]
    field_simp
    <;> ring
  · intro z hz
    exact mul_nonneg (div_nonneg (by nlinarith) (sq_nonneg _)) (sq_nonneg _)

theorem volume_cone_upper {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (diskSolid a 1 (fun z => 1-z^2)) =
      ENNReal.ofReal (Real.pi * (2/3-a+a^3/3)) := by
  rw [volume_diskSolid a 1 ha1 _ (by fun_prop)]
  · congr 1
    have hp : IntervalIntegrable (fun z : ℝ => z^2) volume a 1 :=
      (show Continuous (fun z : ℝ => z^2) by fun_prop).intervalIntegrable a 1
    rw [intervalIntegral.integral_sub (f := fun _ => (1 : ℝ))
        (g := fun z => z^2) intervalIntegrable_const hp,
      intervalIntegral.integral_const,integral_pow]
    simp only [smul_eq_mul]
    ring
  · intro z hz
    nlinarith [hz.1,hz.2]

end
end D4Bound.SphereMeasure
