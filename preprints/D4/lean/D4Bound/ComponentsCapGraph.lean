import D4Bound.ComponentsObtuse
import D4Bound.Geometry

/-! The degree-four projection lemma for the near and narrow antipodal graphs.
This lemma uses affine independence, rather than a cited spherical code bound.
-/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.Components
noncomputable section
open Classical

theorem cap_card_le_four (Z : Finset R4) (w : R4) (hw : ‖w‖ = 1)
    (a s : ℝ) (ha : 0 ≤ a) (has : s < a^2)
    (hcap : ∀ z ∈ Z, a ≤ ⟪z,w⟫)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ⟪z,z'⟫ ≤ s) : Z.card ≤ 4 := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
  have hww : ⟪w,w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  let W := (ℝ ∙ w)ᗮ
  have hmem (z : R4) : z-⟪z,w⟫ • w ∈ W := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, real_inner_smul_right, hww, mul_one, real_inner_comm w z]
    exact sub_self _
  let v : Z → W := fun z => ⟨(z : R4)-⟪(z : R4),w⟫ • w, hmem z⟩
  have he (z z' : Z) : ⟪v z,v z'⟫ =
      ⟪(z : R4),(z' : R4)⟫-⟪(z : R4),w⟫*⟪(z' : R4),w⟫ := by
    change ⟪(z : R4)-⟪(z : R4),w⟫ • w,
      (z' : R4)-⟪(z' : R4),w⟫ • w⟫ = _
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hww]
    rw [real_inner_comm w (z' : R4)]
    ring
  have hi : AffineIndependent ℝ v := affineIndependent_of_inner_neg v (by
    intro z z' hne
    rw [he]
    have hz := hcap z z.property
    have hz' := hcap z' z'.property
    have hp : a*a ≤ ⟪(z : R4),w⟫*⟪(z' : R4),w⟫ :=
      mul_le_mul hz hz' ha (ha.trans hz)
    have hs := hsep z z.property z' z'.property (by
      intro e
      exact hne (Subtype.ext e))
    nlinarith)
  have : Fact (Module.finrank ℝ R4 = 3+1) := ⟨by simp⟩
  have hW : Module.finrank ℝ W = 3 := Submodule.finrank_orthogonal_span_singleton hw0
  have hc := hi.card_le_finrank_succ
  have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range v))
  have h := hc.trans (Nat.add_le_add_right hd 1)
  rw [hW] at h
  simpa only [Fintype.card_coe] using h

/-- The same cap bound for nonzero displacement vectors, with normalization
performed inside the theorem. -/
theorem cap_card_le_four_of_cos (Z : Finset R4) (w : R4) (hw : ‖w‖ = 1)
    (a s : ℝ) (ha : 0 ≤ a) (has : s < a^2) (hs : s < 1)
    (h0 : ∀ z ∈ Z, z ≠ 0)
    (hcap : ∀ z ∈ Z, a ≤ ⟪dir z,w⟫)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      ⟪z,z'⟫ ≤ s*(‖z‖*‖z'‖)) : Z.card ≤ 4 := by
  have hinj := dir_injOn hs h0 hsep
  rw [← Finset.card_image_of_injOn hinj]
  apply cap_card_le_four (Z.image dir) w hw a s ha has
  · intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    exact hcap z hz
  · intro v hv v' hv' hne
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z',hz',rfl⟩ := Finset.mem_image.mp hv'
    exact inner_dir_le (h0 z hz) (h0 z' hz')
      (hsep z hz z' hz' (fun e => hne (congrArg dir e)))

end
end D4Bound.Components
