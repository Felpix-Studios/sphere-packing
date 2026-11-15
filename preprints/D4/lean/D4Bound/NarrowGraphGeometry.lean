import D4Bound.ComponentsCapGraph
import D4Bound.AnnularCert
import D4Bound.GraphSlack

/-! The narrow antipodal graph on the broad annulus has at most 604 ordered
edges: 151 vertices and at most four neighbours per vertex. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
noncomputable section
open Classical

def narrowAntipodalEdge (x y : E4) : Prop :=
  33/28 ≤ ‖x‖ ∧ ‖x‖ ≤ 7/4 ∧ 33/28 ≤ ‖y‖ ∧ ‖y‖ ≤ 7/4 ∧
    ⟪dir x, dir y⟫ ≤ -(183/200)

def narrowAntipodalEdges (X : Finset E4) : ℕ :=
  ∑ x ∈ X, (X.filter fun y => narrowAntipodalEdge x y).card

theorem narrowAntipodal_degree_le {X : Finset E4} (hX : Admissible X)
    (x : E4) : (X.filter fun y => narrowAntipodalEdge x y).card ≤ 4 := by
  let Z := X.filter fun y => narrowAntipodalEdge x y
  by_cases hx0 : x = 0
  · subst x
    have he : Z = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro y hy h
      have := h.1
      norm_num at this
    change Z.card ≤ 4
    rw [he]
    norm_num
  have hz (y : E4) (hy : y ∈ Z) : y ∈ X ∧ narrowAntipodalEdge x y :=
    Finset.mem_filter.mp hy
  apply Components.cap_card_le_four_of_cos Z (-dir x)
    (by rw [norm_neg, norm_dir hx0]) (183/200) (41/49)
    (by norm_num) (by norm_num) (by norm_num)
  · intro y hy e
    have := (hz y hy).2.2.2.1
    rw [e, norm_zero] at this
    norm_num at this
  · intro y hy
    rw [inner_neg_right, real_inner_comm]
    linarith [(hz y hy).2.2.2.2.2]
  · intro y hy z hz' hne
    exact annulus_inner_le (hz y hy).2.2.2.1 (hz y hy).2.2.2.2.1
      (hz z hz').2.2.2.1 (hz z hz').2.2.2.2.1
      (hX.2 y (hz y hy).1 z (hz z hz').1 hne)

theorem narrowAntipodalEdges_le {X : Finset E4} (hX : Admissible X) :
    narrowAntipodalEdges X ≤ 604 := by
  let V := X.filter fun x => 33/28 ≤ ‖x‖ ∧ ‖x‖ ≤ 7/4
  have he : narrowAntipodalEdges X =
      ∑ x ∈ V, (X.filter fun y => narrowAntipodalEdge x y).card := by
    unfold narrowAntipodalEdges V
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs with hr
    · rfl
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun _ _ h => hr ⟨h.1,h.2.1⟩
  rw [he]
  calc
    _ ≤ ∑ _x ∈ V, 4 := Finset.sum_le_sum fun x _ => narrowAntipodal_degree_le hX x
    _ = 4 * V.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 4 * 151 := Nat.mul_le_mul_left 4 (broad_vertices_le annular_151_proved hX)
    _ = 604 := by norm_num

end
end D4Bound
