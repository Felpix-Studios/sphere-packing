import D4Bound.V7SphericalScalar
import D4Bound.Geometry

/-! Transfer spherical scalar upper bounds to the actual local V7 energy,
including points beyond the near radius and closed radial boundaries. -/
set_option maxHeartbeats 0
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

lemma sum_equivFin (S : Finset E4) (f : E4 → ℝ) :
    (∑ i : Fin S.card, f (S.equivFin.symm i)) = ∑ x ∈ S, f x := by
  rw [← S.sum_attach,Finset.attach_eq_univ]
  exact S.equivFin.symm.sum_comp (fun x : S => f x)

lemma sum_double_equivFin (S : Finset E4) (f : E4 → E4 → ℝ) :
    (∑ i : Fin S.card, ∑ j : Fin S.card, f (S.equivFin.symm i) (S.equivFin.symm j)) =
      ∑ x ∈ S, ∑ y ∈ S, f x y := by
  simp_rw [sum_equivFin]
  exact sum_equivFin S (fun x => ∑ y ∈ S, f x y)

/-- A spherical upper bound on the normalized directions gives an exact lower
bound for the two V7 spherical components together. -/
theorem spherical_energy_ge_of_upper (X : Finset E4) (hX : Admissible X)
    (R s B : ℝ) (hR2 : R^2 ≤ 2) (hs : 1-1/(2*R^2) ≤ s)
    (hR : ∀ x ∈ X, ‖x‖ ≤ R5 → ‖x‖ ≤ R)
    (hupper : ∀ x : Fin (nearCount X) → E4, (∀ i, ‖x i‖=1) →
      (∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s) → (∑ i, ∑ j, sphericalScalar ⟪x i,x j⟫) ≤ B) :
    sphericalBound*(nearCount X:ℝ)-sphericalNormalization*B ≤ sphericalEnergy X := by
  let S : Finset E4 := X.filter (fun x => ‖x‖ ≤ R5)
  let e : Fin S.card ≃ S := S.equivFin.symm
  let z : Fin S.card → E4 := fun i => (e i).val
  have hz : ∀ i, z i ∈ X ∧ ‖z i‖ ≤ R5 := fun i => Finset.mem_filter.mp (e i).property
  have hn : ∀ i, z i ≠ 0 := by
    intro i he
    have h := hX.1 (z i) (hz i).1
    rw [he,norm_zero] at h
    norm_num at h
  let x : Fin S.card → E4 := fun i => dir (z i)
  have hx : ∀ i, ‖x i‖=1 := fun i => norm_dir (hn i)
  have hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s := by
    intro i j hij
    have hne : z i ≠ z j := by
      intro he
      exact hij (e.injective (Subtype.ext he))
    have h := shell_inner_le (hX.1 _ (hz i).1) (hR _ (hz i).1 (hz i).2)
      (hX.1 _ (hz j).1) (hR _ (hz j).1 (hz j).2) hR2
      (hX.2 _ (hz i).1 _ (hz j).1 hne)
    exact (inner_dir_le (hn i) (hn j) h).trans hs
  have hub := hupper x hx hxs
  change (∑ i : Fin S.card, ∑ j : Fin S.card, sphericalScalar ⟪x i,x j⟫) ≤ B at hub
  have he : (∑ i, ∑ j, sphericalScalar ⟪x i,x j⟫) =
      ∑ p ∈ S, ∑ q ∈ S, sphericalScalar (⟪p,q⟫/(‖p‖*‖q‖)) := by
    simp only [x,inner_dir]
    exact sum_double_equivFin S (fun p q => sphericalScalar (⟪p,q⟫/(‖p‖*‖q‖)))
  rw [he] at hub
  rw [spherical_energy_identity]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hub sphericalNormalization_pos.le) _

lemma all_le_R4_of_first_le_four {X : Finset E4} (h : firstRadius X ≤ 4) :
    ∀ x ∈ X, ‖x‖ ≤ R5 → ‖x‖ ≤ R4 := by
  have h14 : R1 ≤ R4 := by norm_num [R1,R4]
  have h24 : R2 ≤ R4 := by norm_num [R2,R4]
  have h34 : R3 ≤ R4 := by norm_num [R3,R4]
  have h45 : R4 ≤ R5 := by norm_num [R4,R5]
  have mono : ∀ {r s : ℝ}, r ≤ s → countWithin X r ≤ countWithin X s := by
    intro r s hrs
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.trans hrs⟩
  have hc : countWithin X R4=nearCount X := by
    unfold firstRadius at h
    split_ifs at h with h1 h2 h3 h4
    · exact le_antisymm (mono h45) ((by rw [← h1]; exact mono h14))
    · exact le_antisymm (mono h45) ((by rw [← h2]; exact mono h24))
    · exact le_antisymm (mono h45) ((by rw [← h3]; exact mono h34))
    · exact h4
    · omega
  have hsub : (X.filter fun x => ‖x‖ ≤ R4) ⊆ X.filter fun x => ‖x‖ ≤ R5 :=
    fun x hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.trans h45⟩
  have heq : (X.filter fun x => ‖x‖ ≤ R4)=X.filter fun x => ‖x‖ ≤ R5 :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [countWithin,nearCount] using hc.ge)
  intro x hx h5
  have hm : x ∈ X.filter fun x => ‖x‖ ≤ R4 := by rw [heq]; exact Finset.mem_filter.mpr ⟨hx,h5⟩
  exact (Finset.mem_filter.mp hm).2

#print axioms spherical_energy_ge_of_upper
end
end D4Bound.V7
