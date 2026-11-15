import D4Bound.NearGraphCount
import D4Bound.ComponentsCapGraph
import D4Bound.CountDomain

/-! The closed near-antipodal graph has at most 120 ordered edges.
The vertex count and degree bound are both proved, without spherical-code premises.
-/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
noncomputable section
open Classical

def nearAntipodalEdge (x y : E4) : Prop :=
  ‖x‖ ≤ 103/100 ∧ ‖y‖ ≤ 103/100 ∧ ⟪dir x, dir y⟫ ≤ -(3/4)

def nearAntipodalEdges (X : Finset E4) : ℕ :=
  ∑ x ∈ X, (X.filter fun y => nearAntipodalEdge x y).card

theorem near_shell_count_le {X : Finset E4} (hX : Admissible X) :
    countWithin X (103/100) ≤ 30 :=
  countWithin_le_of_code NearGraphCertificate.code_thirty
    (by norm_num) (by norm_num) (by norm_num) hX

theorem near_shell_inner {X : Finset E4} (hX : Admissible X)
    {x y : E4} (hx : x ∈ X) (hy : y ∈ X) (hxr : ‖x‖ ≤ 103/100)
    (hyr : ‖y‖ ≤ 103/100) (hne : x ≠ y) :
    ⟪x,y⟫ ≤ (5609/10609) * (‖x‖*‖y‖) := by
  convert shell_inner_le (hX.1 x hx) hxr (hX.1 y hy) hyr
    (by norm_num : (103/100 : ℝ)^2 ≤ 2) (hX.2 x hx y hy hne) using 1 <;> norm_num

theorem nearAntipodal_degree_le {X : Finset E4} (hX : Admissible X)
    {x : E4} (hx : x ∈ X) : (X.filter fun y => nearAntipodalEdge x y).card ≤ 4 := by
  let Z := X.filter fun y => nearAntipodalEdge x y
  have hx0 : x ≠ 0 := by
    intro e
    have := hX.1 x hx
    norm_num [e] at this
  have hz (y : E4) (hy : y ∈ Z) : y ∈ X ∧ nearAntipodalEdge x y :=
    Finset.mem_filter.mp hy
  have hz0 (y : E4) (hy : y ∈ Z) : y ≠ 0 := by
    intro e
    have := hX.1 y (hz y hy).1
    norm_num [e] at this
  have hc : ∀ y ∈ Z, ∀ z ∈ Z, y ≠ z →
      ⟪y,z⟫ ≤ (5609/10609) * (‖y‖*‖z‖) := by
    intro y hy z hz' hne
    exact near_shell_inner hX (hz y hy).1 (hz z hz').1
      (hz y hy).2.2.1 (hz z hz').2.2.1 hne
  have hinj : Set.InjOn dir (Z : Set E4) := dir_injOn (by norm_num) hz0 hc
  change Z.card ≤ 4
  rw [← Finset.card_image_of_injOn hinj]
  apply Components.cap_card_le_four (Z.image dir) (-dir x)
    (by rw [norm_neg, norm_dir hx0]) (3/4) (5609/10609) (by norm_num) (by norm_num)
  · intro v hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    rw [inner_neg_right, real_inner_comm]
    linarith [(hz y hy).2.2.2]
  · intro v hv w hw hne
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z,hz',rfl⟩ := Finset.mem_image.mp hw
    exact inner_dir_le (hz0 y hy) (hz0 z hz')
      (hc y hy z hz' (fun e => hne (congrArg dir e)))

theorem nearAntipodalEdges_le {X : Finset E4} (hX : Admissible X) :
    nearAntipodalEdges X ≤ 120 := by
  let V := X.filter fun x => ‖x‖ ≤ 103/100
  have he : nearAntipodalEdges X =
      ∑ x ∈ V, (X.filter fun y => nearAntipodalEdge x y).card := by
    unfold nearAntipodalEdges V
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs with hr
    · rfl
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun _ _ h => hr h.1
  rw [he]
  calc
    _ ≤ ∑ _x ∈ V, 4 := Finset.sum_le_sum fun x hx =>
      nearAntipodal_degree_le hX (Finset.mem_filter.mp hx).1
    _ = 4 * V.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 4 * 30 := Nat.mul_le_mul_left 4 (near_shell_count_le hX)
    _ = 120 := by norm_num

end
end D4Bound
