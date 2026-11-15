import D4Bound.V7CapsGeometry
import D4Bound.V7CapsAverage

/-! Transport a genuine transverse spherical law to the concrete cap probabilities. -/
open Finset MeasureTheory
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

/-- Analytic interface supplied by the transverse two-sphere probability theorem. -/
def TransverseLaw (e : E4) (μ : Measure E4) : Prop :=
  (∀ᵐ u ∂μ, ‖u‖ = 1 ∧ ⟪e,u⟫ = 0) ∧
  ∀ z : E4, z ≠ 0 → ⟪z,e⟫ = 0 → ∀ a : ℝ,
    Integrable (fun u => if a ≤ ⟪z,u⟫ then (1 : ℝ) else 0) μ ∧
    (∫ u, (if a ≤ ⟪z,u⟫ then (1 : ℝ) else 0) ∂μ) =
      max 0 (min 1 ((1-a/‖z‖)/2))

theorem capProbe_marginal {c : Cap} (hc : CapValid c) {x y : E4}
    (hx : x ≠ 0) (hy : y ≠ 0) (μ : Measure E4) [IsProbabilityMeasure μ]
    (hlaw : TransverseLaw (dir y) μ) :
    Integrable (fun u => probeIndicator c x (capProbe c (dir y) u)) μ ∧
    capProbability c ‖x‖ (⟪x,y⟫/(‖x‖*‖y‖)) =
      ∫ u, probeIndicator c x (capProbe c (dir y) u) ∂μ := by
  let z := capTransverse c (dir x) (dir y)
  let t := ⟪x,y⟫/(‖x‖*‖y‖)
  let a := (‖x‖*‖x‖+(c.d : ℝ)^2-(c.a2 : ℝ))/(2*(c.d : ℝ)*‖x‖) -
    (c.sigma : ℝ)*t
  let S := (1-(c.sigma : ℝ)^2)*(1-t*t)
  have hz : ‖z‖^2 = S := by
    simpa only [z, S, t, inner_dir] using capTransverse_norm_sq hc (norm_dir hx) (norm_dir hy)
  have hzorth : ⟪z,dir y⟫ = 0 := capTransverse_orthogonal c (dir x) (dir y) (norm_dir hy)
  have hae : (fun u => probeIndicator c x (capProbe c (dir y) u)) =ᵐ[μ]
      (fun u => if a ≤ ⟪z,u⟫ then (1 : ℝ) else 0) := by
    filter_upwards [hlaw.1] with u hu
    unfold probeIndicator
    simp only [capProbe_membership hc hx (norm_dir hy) hu.1 hu.2, inner_dir, a, t, z]
  have hformula : capProbability c ‖x‖ t =
      if S = 0 then (if a ≤ 0 then 1 else 0)
      else max 0 (min 1 ((1-a/Real.sqrt S)/2)) := rfl
  by_cases hz0 : z = 0
  · have hS : S = 0 := by simpa [hz0] using hz.symm
    have hconst : (fun u => if a ≤ ⟪z,u⟫ then (1 : ℝ) else 0) =
        (fun _u : E4 => if a ≤ 0 then (1 : ℝ) else 0) := by
      simp only [hz0, inner_zero_left]
    rw [hconst] at hae
    refine ⟨(integrable_const _).congr hae.symm, ?_⟩
    change capProbability c ‖x‖ t = _
    rw [hformula, if_pos hS, integral_congr_ae hae]
    simp
  · obtain ⟨hint,heq⟩ := hlaw.2 z hz0 hzorth a
    have hS : S ≠ 0 := by
      intro hs
      have hn := norm_pos_iff.mpr hz0
      nlinarith [hz]
    have hsqrt : Real.sqrt S = ‖z‖ := by
      rw [← hz, Real.sqrt_sq (norm_nonneg z)]
    refine ⟨hint.congr hae.symm, ?_⟩
    change capProbability c ‖x‖ t = _
    rw [hformula, if_neg hS, hsqrt, integral_congr_ae hae, heq]

theorem cap_capacity_of_transverse_laws {c : Cap} (hc : CapValid c)
    (hlaws : ∀ e : E4, ‖e‖ = 1 → ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧ TransverseLaw e μ) : CapProbabilityCapacity c := by
  apply cap_capacity_of_parametrized_measure (Ω := E4) hc
  intro y hy
  obtain ⟨μ,hprob,hlaw⟩ := hlaws (dir y) (norm_dir hy)
  letI : IsProbabilityMeasure μ := hprob
  refine ⟨μ,capProbe c (dir y),hprob,?_,?_,?_⟩
  · filter_upwards [hlaw.1] with u hu
    exact capProbe_norm hc (norm_dir hy) hu.1 hu.2
  · intro x hx
    exact (capProbe_marginal hc hx hy μ hlaw).1
  · intro x hx
    exact (capProbe_marginal hc hx hy μ hlaw).2

theorem caps_energy_nonneg_of_transverse_laws
    (hlaws : ∀ e : E4, ‖e‖ = 1 → ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧ TransverseLaw e μ)
    {X : Finset E4} (hX : Admissible X) (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) :
    0 ≤ capsEnergy X := by
  apply caps_energy_nonneg_of_capacities _ hX hR
  intro c hc
  exact cap_capacity_of_transverse_laws (caps_data_valid c hc) hlaws

end
end D4Bound.V7
