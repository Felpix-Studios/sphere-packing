import D4Bound.ModerateGraphBound
import D4Bound.Neighbourhood

/-! Transfer the 1880-edge spherical bound to the actual closed radial shell. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
noncomputable section
open Classical

theorem relationCount_image {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (r : β → β → Prop) (hf : Set.InjOn f (s : Set α)) :
    relationCount (s.image f) r = relationCount s (fun x y => r (f x) (f y)) := by
  unfold relationCount
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_image hf
  · exact hf

theorem moderate_annulus_inner {x y : E4}
    (hx : 7/5 ≤ ‖x‖) (hx' : ‖x‖ ≤ 3/2)
    (hy : 7/5 ≤ ‖y‖) (hy' : ‖y‖ ≤ 3/2) (hsep : 1 ≤ ‖x-y‖) :
    ⟪x,y⟫ ≤ (7/9)*(‖x‖*‖y‖) := by
  have h := two_inner_le_of_sep hsep
  have hs : 9*(‖x‖^2+‖y‖^2-1) ≤ 14*(‖x‖*‖y‖) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy),
      mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy'),
      mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy),
      mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy'),
      mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx'),
      mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hy')]
  linarith

def moderateGraphVertices (X : Finset E4) : Finset E4 :=
  X.filter fun x => 7/5 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2

def moderateGraphEdges (X : Finset E4) : ℕ :=
  relationCount (moderateGraphVertices X)
    (fun x y => -4/5 ≤ ⟪dir x,dir y⟫ ∧ ⟪dir x,dir y⟫ ≤ -11/20)

theorem moderateGraphEdges_le {X : Finset E4} (hX : Admissible X) :
    moderateGraphEdges X ≤ 1880 := by
  let V := moderateGraphVertices X
  have hv (x : E4) (hx : x ∈ V) : x ∈ X ∧ 7/5 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2 :=
    Finset.mem_filter.mp hx
  have hv0 (x : E4) (hx : x ∈ V) : x ≠ 0 := by
    intro e
    have := (hv x hx).2.1
    norm_num [e] at this
  have hs : ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      ⟪x,y⟫ ≤ (7/9)*(‖x‖*‖y‖) := by
    intro x hx y hy hne
    exact moderate_annulus_inner (hv x hx).2.1 (hv x hx).2.2
      (hv y hy).2.1 (hv y hy).2.2 (hX.2 x (hv x hx).1 y (hv y hy).1 hne)
  have hinj := dir_injOn (by norm_num : (7/9 : ℝ) < 1) hv0 hs
  have hc := moderate_angular_edges_le (V.image dir)
    (by intro u hu; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu; exact norm_dir (hv0 x hx))
    (by
      intro u hu v hv' hne
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv'
      exact inner_dir_le (hv0 x hx) (hv0 y hy)
        (hs x hx y hy (fun e => hne (congrArg dir e))))
  have hc' : relationCount (V.image dir)
      (fun x y : E4 => -4/5 ≤ ⟪x,y⟫ ∧ ⟪x,y⟫ ≤ -11/20) ≤ 1880 := by
    simpa [angularBandCount] using hc
  have he := relationCount_image V (dir : E4 → E4)
    (fun x y : E4 => -4/5 ≤ ⟪x,y⟫ ∧ ⟪x,y⟫ ≤ -11/20) hinj
  simpa [moderateGraphEdges,V] using he.symm.le.trans hc'

end
end D4Bound
