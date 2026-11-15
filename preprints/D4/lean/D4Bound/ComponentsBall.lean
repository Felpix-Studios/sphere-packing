import D4Bound.ComponentsObtuse

/-! The strict-radius, dimension-dependent branch of the pointed-cap count.
The hypotheses concern a closed ball; strictness is in the radius bound.
-/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.Components
noncomputable section
open Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem card_le_finrank_succ_of_ball_sq (X : Finset V) (hX : UnitSep X)
    (a : ℝ) (ha : a < 1/2) (hball : ∀ x ∈ X, ‖x‖^2 ≤ a) :
    X.card ≤ Module.finrank ℝ V + 1 := by
  apply card_le_finrank_succ_of_inner_neg X
  intro x hx y hy hxy
  have hs := hX x hx y hy hxy
  have hsq : 1 ≤ ‖x-y‖^2 := by nlinarith
  rw [norm_sub_sq_real] at hsq
  nlinarith [hball x hx, hball y hy]

theorem card_le_finrank_succ_of_closed_ball (X : Finset V) (hX : UnitSep X)
    (c : V) (a : ℝ) (ha : a < 1/2)
    (hball : ∀ x ∈ X, ‖x-c‖^2 ≤ a) :
    X.card ≤ Module.finrank ℝ V + 1 := by
  have hinj : Set.InjOn (fun x : V => x-c) X :=
    fun x _ y _ hxy => sub_left_inj.mp hxy
  have hsep : UnitSep (X.image fun x => x-c) := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    have hne : x' ≠ y' := fun he => hxy (by rw [he])
    simpa only [sub_sub_sub_cancel_right] using hX x' hx' y' hy' hne
  have hb : ∀ x ∈ X.image (fun x => x-c), ‖x‖^2 ≤ a := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hball y hy
  have hc := card_le_finrank_succ_of_ball_sq _ hsep a ha hb
  rwa [Finset.card_image_of_injOn hinj] at hc

theorem card_le_five_of_closed_ball (X : Finset R4) (hX : UnitSep X)
    (c : R4) (a : ℝ) (ha : a < 1/2)
    (hball : ∀ x ∈ X, ‖x-c‖^2 ≤ a) : X.card ≤ 5 := by
  simpa [R4] using card_le_finrank_succ_of_closed_ball X hX c a ha hball

end
end D4Bound.Components
