import D4Bound.SphereMeasureSector
import D4Bound.V7CapsMeasure

/-! Transport the common three-dimensional spherical probability measure to
the orthogonal complement of any unit vector in four dimensions. The sole
analytic input is the spherical cap formula, supplied explicitly here so
that the geometric transport is independent of its cone-volume proof. -/
open MeasureTheory
open scoped RealInnerProductSpace
namespace D4Bound.SphereMeasure
noncomputable section
open Classical

theorem transverse_laws_of_cap_formula
    (hcap : ∀ v : R3, ‖v‖ = 1 → ∀ a : ℝ,
      uniformSphere.real (cap v a) = clip ((1-a)/2)) :
    ∀ e : E4, ‖e‖ = 1 → ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧ V7.TransverseLaw e μ := by
  intro e he
  have he0 : e ≠ 0 := by
    intro h
    simp only [h,norm_zero] at he
    norm_num at he
  have : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
  have hdim : Module.finrank ℝ (ℝ ∙ e)ᗮ = 3 :=
    Submodule.finrank_orthogonal_span_singleton he0
  let L : R3 ≃ₗᵢ[ℝ] (ℝ ∙ e)ᗮ :=
    (((stdOrthonormalBasis ℝ (ℝ ∙ e)ᗮ).reindex (finCongr hdim)).repr).symm
  let f : UnitSphere → E4 := fun u => (L (u : R3) : E4)
  have hf : Measurable f := by
    exact (continuous_subtype_val.comp
      (L.continuous.comp continuous_subtype_val)).measurable
  let μ : Measure E4 := Measure.map f uniformSphere
  have hprob : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure μ := hprob
  refine ⟨μ,hprob,?_⟩
  apply V7.transverseLaw_of_unit_tail μ
  · change ∀ᵐ u ∂Measure.map f uniformSphere, ‖u‖ = 1 ∧ ⟪e,u⟫ = 0
    apply (ae_map_iff hf.aemeasurable (by measurability)).mpr
    apply Filter.Eventually.of_forall
    intro u
    constructor
    · change ‖L (u : R3)‖ = 1
      rw [L.norm_map]
      simpa only [Metric.mem_sphere,dist_zero_right] using u.property
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (L (u : R3)).property
  · intro z hz hze a
    have hzm : z ∈ (ℝ ∙ e)ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hze
    let z' : (ℝ ∙ e)ᗮ := ⟨z,hzm⟩
    let v : R3 := L.symm z'
    have hv : ‖v‖ = 1 := by
      dsimp only [v]
      rw [L.symm.norm_map]
      exact hz
    have hinner (u : UnitSphere) : ⟪z,f u⟫ = ⟪(u : R3),v⟫ := by
      calc
        ⟪z,f u⟫ = ⟪z',L (u : R3)⟫ := rfl
        _ = ⟪L v,L (u : R3)⟫ := by simp only [v,L.apply_symm_apply]
        _ = ⟪v,(u : R3)⟫ := L.inner_map_map _ _
        _ = ⟪(u : R3),v⟫ := real_inner_comm _ _
    have hm : MeasurableSet {u : E4 | a ≤ ⟪z,u⟫} :=
      measurableSet_le measurable_const (continuous_const.inner continuous_id).measurable
    have hpre : f ⁻¹' {u : E4 | a ≤ ⟪z,u⟫} = cap v a := by
      ext u
      simp only [Set.mem_preimage,Set.mem_setOf_eq,cap,hinner]
    change (Measure.map f uniformSphere).real {u : E4 | a ≤ ⟪z,u⟫} = _
    rw [map_measureReal_apply hf hm,hpre]
    exact hcap v hv a

end
end D4Bound.SphereMeasure
