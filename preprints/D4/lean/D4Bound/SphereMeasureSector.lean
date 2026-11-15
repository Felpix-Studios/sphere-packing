import D4Bound.SphereMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Relating spherical caps to three-dimensional conical sectors. -/
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Pointwise
namespace D4Bound.SphereMeasure
noncomputable section
open Classical

def cap (v : R3) (a : ℝ) : Set UnitSphere := {u | a ≤ ⟪(u : R3),v⟫}

def openSector (v : R3) (a : ℝ) : Set R3 :=
  {x | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ a*‖x‖ ≤ ⟪x,v⟫}

def closedSector (v : R3) (a : ℝ) : Set R3 :=
  {x | ‖x‖ ≤ 1 ∧ a*‖x‖ ≤ ⟪x,v⟫}

theorem cap_measurable (v : R3) (a : ℝ) : MeasurableSet (cap v a) := by
  apply measurableSet_le measurable_const
  exact (continuous_subtype_val.inner continuous_const).measurable

theorem openSector_measurable (v : R3) (a : ℝ) : MeasurableSet (openSector v a) := by
  exact ((measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)).inter
      (measurableSet_le (measurable_const.mul measurable_norm)
        (continuous_id.inner continuous_const).measurable) |>.congr (by
          ext x
          simp only [openSector,mem_setOf_eq,mem_inter_iff]
          tauto)

theorem closedSector_measurable (v : R3) (a : ℝ) : MeasurableSet (closedSector v a) := by
  exact (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le (measurable_const.mul measurable_norm)
      (continuous_id.inner continuous_const).measurable)

theorem radial_cap_eq_sector (v : R3) (a : ℝ) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' cap v a) = openSector v a := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨u,hu,rfl⟩,rfl⟩
    have hun : ‖(u : R3)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.property
    have hrn : ‖r • (u : R3)‖ = r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,hun,mul_one]
    change 0 < ‖r • (u : R3)‖ ∧ ‖r • (u : R3)‖ < 1 ∧
      a*‖r • (u : R3)‖ ≤ ⟪r • (u : R3),v⟫
    rw [hrn,real_inner_smul_left]
    exact ⟨hr.1,hr.2,by have := mul_le_mul_of_nonneg_left hu hr.1.le; nlinarith⟩
  · rintro ⟨hx0,hx1,hxv⟩
    let u : UnitSphere := ⟨‖x‖⁻¹ • x, by
      rw [Metric.mem_sphere,dist_zero_right]
      exact norm_smul_inv_norm (norm_pos_iff.mp hx0)⟩
    refine ⟨‖x‖,⟨hx0,hx1⟩,u,⟨u,?_,rfl⟩,?_⟩
    · change a ≤ ⟪‖x‖⁻¹ • x,v⟫
      rw [real_inner_smul_left,← div_eq_inv_mul]
      exact (le_div_iff₀ hx0).mpr hxv
    · change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul,mul_inv_cancel₀ hx0.ne',one_smul]

theorem area_cap_eq_sector (v : R3) (a : ℝ) :
    area (cap v a) = 3 * volume (openSector v a) := by
  rw [area,Measure.toSphere_apply' _ (cap_measurable v a),radial_cap_eq_sector]
  simp

theorem sector_rotation (e : R3 ≃ₗᵢ[ℝ] R3) (v : R3) (a : ℝ) :
    e ⁻¹' openSector (e v) a = openSector v a := by
  ext x
  simp only [openSector,mem_preimage,mem_setOf_eq,LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.inner_map_map]

theorem area_cap_rotation (e : R3 ≃ₗᵢ[ℝ] R3) (v : R3) (a : ℝ) :
    area (cap (e v) a) = area (cap v a) := by
  rw [area_cap_eq_sector,area_cap_eq_sector]
  congr 1
  rw [← sector_rotation e v a]
  exact (e.measurePreserving.measure_preimage
    (openSector_measurable (e v) a).nullMeasurableSet).symm

theorem uniformSphere_cap_rotation (e : R3 ≃ₗᵢ[ℝ] R3) (v : R3) (a : ℝ) :
    uniformSphere.real (cap (e v) a) = uniformSphere.real (cap v a) := by
  unfold uniformSphere
  rw [measureReal_ennreal_smul_apply,measureReal_ennreal_smul_apply]
  congr 1
  unfold Measure.real
  rw [area_cap_rotation e v a]

/-- Once a pole has been computed, every other unit direction has the same law. -/
theorem uniformSphere_cap_eq_of_norm_eq {v w : R3} (h : ‖v‖ = ‖w‖) (a : ℝ) :
    uniformSphere.real (cap v a) = uniformSphere.real (cap w a) := by
  let e := (ℝ ∙ (v-w))ᗮ.reflection
  have he : e v = w := Submodule.reflection_sub h
  rw [← he]
  exact (uniformSphere_cap_rotation e v a).symm

end
end D4Bound.SphereMeasure
