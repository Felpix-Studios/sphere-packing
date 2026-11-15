import D4Bound.SphericalCertLegendre
import D4Bound.GraphSlack

/-! S2 polynomial kernels on the orthogonal complement of an anchor in R4. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound

lemma nsq_of_euclidean3 (v : EuclideanSpace ℝ (Fin 3)) :
    Schoenberg2.nsq (fun a => (WithLp.ofLp v) a) = ‖v‖^2 := by
  have h := EuclideanSpace.norm_eq v
  have h' := congrArg (· ^ 2) h
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h'
  simpa [Schoenberg2.nsq,Real.norm_eq_abs,sq_abs] using h'.symm

lemma solidLegendre_E3_posDef {ι : Type*} (s : Finset ι)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (c : ι → ℝ) (l : ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*
      Schoenberg2.solidLegendre ⟪x i,x j⟫ (‖x i‖^2*‖x j‖^2) l := by
  have h := Schoenberg2.solidLegendre_posDef s (fun i a => (WithLp.ofLp (x i)) a) c l
  convert h using 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [nsq_of_euclidean3,nsq_of_euclidean3]
  simp [PiLp.inner_apply,mul_comm]

/-- No normalization or nonzero assumption on the transverse vectors is necessary. -/
theorem solidLegendre_perp_posDef {ι : Type*} (s : Finset ι) (w : E4) (hw : w ≠ 0)
    (x : ι → E4) (c : ι → ℝ) (l : ℕ) (hx : ∀ i ∈ s, ⟪w,x i⟫ = 0) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*
      Schoenberg2.solidLegendre ⟪x i,x j⟫ (‖x i‖^2*‖x j‖^2) l := by
  classical
  have : Fact (Module.finrank ℝ E4 = 3+1) := ⟨by simp⟩
  have hW : Module.finrank ℝ (ℝ ∙ w)ᗮ = 3 := Submodule.finrank_orthogonal_span_singleton hw
  let e : (ℝ ∙ w)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ((stdOrthonormalBasis ℝ (ℝ ∙ w)ᗮ).reindex (finCongr hW)).repr
  let g : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
    if hi : x i ∈ (ℝ ∙ w)ᗮ then e ⟨x i,hi⟩ else 0
  have hm : ∀ i ∈ s, x i ∈ (ℝ ∙ w)ᗮ := fun i hi =>
    (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr (hx i hi)
  have hg : ∀ i ∈ s, ∀ j ∈ s, ⟪g i,g j⟫ = ⟪x i,x j⟫ := by
    intro i hi j hj
    simp only [g,dif_pos (hm i hi),dif_pos (hm j hj),LinearIsometryEquiv.inner_map_map,
      Submodule.coe_inner]
  have hgn : ∀ i ∈ s, ‖g i‖^2 = ‖x i‖^2 := by
    intro i hi
    simpa only [real_inner_self_eq_norm_sq] using hg i hi i hi
  have h := solidLegendre_E3_posDef s g c l
  convert h using 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [hg i hi j hj,hgn i hi,hgn j hj]

/-- The certificate's `H_l(a,b,t)` is PSD on the actual projected neighbours. -/
theorem anchored_legendre_posDef {ι : Type*} (s : Finset ι) (w : E4) (hw : ‖w‖=1)
    (x : ι → E4) (hx : ∀ i ∈ s, ‖x i‖=1) (c : ι → ℝ) (l : ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*
      Schoenberg2.solidLegendre (⟪x i,x j⟫-⟪w,x i⟫*⟪w,x j⟫)
        ((1-⟪w,x i⟫^2)*(1-⟪w,x j⟫^2)) l := by
  let p : ι → E4 := fun i => x i - ⟪w,x i⟫ • w
  have hww : ⟪w,w⟫ = (1:ℝ) := by rw [real_inner_self_eq_norm_sq,hw]; norm_num
  have hp : ∀ i, ⟪w,p i⟫=0 := by intro i; simp [p,inner_sub_right,real_inner_smul_right,hw]
  have hinner : ∀ i j, ⟪p i,p j⟫ = ⟪x i,x j⟫-⟪w,x i⟫*⟪w,x j⟫ := by
    intro i j
    simp only [p,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hww]
    rw [real_inner_comm (x i) w]
    ring
  have hn : ∀ i ∈ s, ‖p i‖^2 = 1-⟪w,x i⟫^2 := by
    intro i hi
    have h := hinner i i
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hx i hi] at h
    nlinarith
  have h := solidLegendre_perp_posDef s w (by intro h; simp [h] at hw) p c l (fun i _ => hp i)
  convert h using 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [hinner,hn i hi,hn j hj]

#print axioms anchored_legendre_posDef
end D4Bound
