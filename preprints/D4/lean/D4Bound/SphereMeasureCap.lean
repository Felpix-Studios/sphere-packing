import D4Bound.SphereMeasureSlices
import D4Bound.SphereMeasureTail

/-! Archimedes' spherical-cap formula, from exact circular-slice integration. -/
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace D4Bound.SphereMeasure
noncomputable section
open Classical

theorem diskSolid_overlap_null (a : ℝ) (f g : ℝ → ℝ) :
    volume (diskSolid 0 a f ∩ diskSolid a 1 g) = 0 := by
  have hs : diskSolid 0 a f ∩ diskSolid a 1 g ⊆
      ({a} : Set ℝ) ×ˢ (univ : Set R2) := by
    intro p hp
    exact ⟨by
      change p.1 = a
      exact le_antisymm hp.1.1.2 hp.2.1.1,mem_univ _⟩
  apply measure_mono_null hs
  change ((volume : Measure ℝ).prod (volume : Measure R2)) ({a} ×ˢ univ) = 0
  rw [Measure.prod_prod,measure_singleton,zero_mul]

theorem volume_sectorSlice {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (sectorSlice a) = ENNReal.ofReal (2*Real.pi*(1-a)/3) := by
  by_cases h0 : a = 0
  · subst a
    rw [sectorSlice_zero,volume_cone_upper (by norm_num) (by norm_num)]
    congr 1
    ring
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rw [sectorSlice_eq_union ha' ha1]
    have hu := measure_union_add_inter (μ := (volume : Measure (ℝ × R2)))
      (diskSolid 0 a (fun z => (1-a^2)/a^2*z^2))
      (diskSolid_measurable a 1 (fun z => 1-z^2) (by fun_prop))
    rw [diskSolid_overlap_null,add_zero] at hu
    rw [hu,volume_cone_lower ha' ha1,volume_cone_upper ha ha1]
    have hlo : 0 ≤ Real.pi*((1-a^2)*a/3) := by
      have hsq : 0 ≤ 1-a^2 := by nlinarith
      positivity
    have hpol : 2/3-a+a^3/3 = (1-a)^2*(a+2)/3 := by ring
    have hhi : 0 ≤ Real.pi*(2/3-a+a^3/3) := by
      rw [hpol]
      positivity
    rw [← ENNReal.ofReal_add hlo hhi]
    congr 1
    ring

theorem volume_closedSector_pole {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (closedSector pole a) = ENNReal.ofReal (2*Real.pi*(1-a)/3) := by
  rw [closedSector_eq_split ha,
    split_measurePreserving.measure_preimage (sectorSlice_measurable a).nullMeasurableSet,
    volume_sectorSlice ha ha1]

theorem area_real_univ : area.real univ = 4*Real.pi := by
  have hv : (volume : Measure R3).real (Metric.ball 0 1) = Real.pi*4/3 := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num [ENNReal.toReal_ofReal,Real.pi_nonneg]
    positivity
  simp only [area,Measure.toSphere_real_apply_univ]
  rw [hv]
  norm_num
  ring

theorem area_real_cap_pole {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    area.real (cap pole a) = 2*Real.pi*(1-a) := by
  change (area (cap pole a)).toReal = _
  rw [area_cap_eq_sector,openSector_volume_eq_closed,volume_closedSector_pole ha ha1,
    ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (by positivity)]
  ring

theorem uniformSphere_cap_pole_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    uniformSphere.real (cap pole a) = (1-a)/2 := by
  rw [uniformSphere,measureReal_ennreal_smul_apply,ENNReal.toReal_inv]
  change (area.real univ)⁻¹ * area.real (cap pole a) = _
  rw [area_real_univ,area_real_cap_pole ha ha1]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem uniformSphere_cap_nonneg (v : R3) (hv : ‖v‖ = 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    uniformSphere.real (cap v a) = (1-a)/2 := by
  rw [uniformSphere_cap_eq_of_norm_eq (hv.trans norm_pole.symm)]
  exact uniformSphere_cap_pole_nonneg ha ha1

/-- Every unit direction has the uniform coordinate law on `[-1,1]`,
including closed tails at the endpoints. -/
theorem uniformSphere_cap (v : R3) (hv : ‖v‖ = 1) (a : ℝ) :
    uniformSphere.real (cap v a) = clip ((1-a)/2) :=
  uniformSphere_cap_of_nonneg uniformSphere_cap_nonneg v hv a

end
end D4Bound.SphereMeasure

#print axioms D4Bound.SphereMeasure.uniformSphere_cap
