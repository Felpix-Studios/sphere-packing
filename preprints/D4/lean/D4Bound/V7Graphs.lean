import D4Bound.V7CountEnergy
import D4Bound.NearGraphGeometry
import D4Bound.NarrowGraphGeometry
import D4Bound.ModerateGraphGeometry

/-! Exact counting identities for the six concrete graph components of V7.
Their zero weights are retained in the identity. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

theorem relationCount_mono {α : Type*} (X : Finset α) (r s : α → α → Prop)
    (h : ∀ x ∈ X, ∀ y ∈ X, r x y → s x y) : relationCount X r ≤ relationCount X s := by
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases hr : r x y
  · simp [hr,h x hx y hy hr]
  · simp [hr]

theorem relationCount_congr {α : Type*} (X : Finset α) (r s : α → α → Prop)
    (h : ∀ x ∈ X, ∀ y ∈ X, r x y ↔ s x y) : relationCount X r = relationCount X s := by
  apply Nat.le_antisymm
  · exact relationCount_mono X r s (fun x hx y hy => (h x hx y hy).mp)
  · exact relationCount_mono X s r (fun x hx y hy => (h x hx y hy).mpr)

theorem relationCount_eq_sum_card {α : Type*} (X : Finset α) (r : α → α → Prop) :
    relationCount X r = ∑ x ∈ X, (X.filter (r x)).card := by
  simp only [relationCount,Finset.card_filter]

theorem relationCount_filter {α : Type*} (X : Finset α) (r : α → α → Prop) (p : α → Prop)
    (h : ∀ x ∈ X, ∀ y ∈ X, r x y → p x ∧ p y) :
    relationCount (X.filter p) r = relationCount X r := by
  unfold relationCount
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hpx : p x
  · rw [if_pos hpx]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hpy : p y
    · simp [hpy]
    · have hn : ¬ r x y := fun hr => hpy (h x hx y hy hr).2
      simp [hpy,hn]
  · rw [if_neg hpx]
    symm
    apply Finset.sum_eq_zero
    intro y hy
    have hn : ¬ r x y := fun hr => hpx (h x hx y hy hr).1
    simp [hn]

def graphSelected (g : Graph) (x y : E4) : Prop :=
  graphRadial g ‖x‖ ‖y‖ ∧ (g.tlo : ℝ) ≤ ⟪dir x,dir y⟫ ∧
    ⟪dir x,dir y⟫ ≤ (g.thi : ℝ)

def graphValue (g : Graph) (X : Finset E4) : ℝ :=
  (g.weight : ℝ)*((g.capacity : ℝ)-(relationCount X (graphSelected g) : ℝ))

theorem graph_pair_sum (g : Graph) (X : Finset E4) :
    (∑ x ∈ X, ∑ y ∈ X,
      if graphRadial g ‖x‖ ‖y‖ ∧ (g.tlo : ℝ) ≤ ⟪x,y⟫/(‖x‖*‖y‖) ∧
          ⟪x,y⟫/(‖x‖*‖y‖) ≤ (g.thi : ℝ) then (g.weight : ℝ) else 0) =
        (g.weight : ℝ)*(relationCount X (graphSelected g) : ℝ) := by
  unfold relationCount graphSelected
  simp only [inner_dir,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> simp

theorem graphs_energy_identity (X : Finset E4) :
    graphsEnergy X = (graphs.map fun g => graphValue g X).sum := by
  unfold graphsEnergy radialEnergy graphOriginQ graphsCorrection
  simp only [Finset.sum_const_zero,mul_zero,add_zero,Finset.sum_neg_distrib]
  simp_rw [sum_list_map,graph_pair_sum]
  generalize graphs = L
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_mul] at ih ⊢
    rw [← ih]
    unfold graphValue
    ring

def graphNear : Graph := graphs[3]
def graphNarrow : Graph := graphs[4]
def graphModerate : Graph := graphs[5]

theorem graphNear_count_le {X : Finset E4} (hX : Admissible X) :
    relationCount X (graphSelected graphNear) ≤ 120 := by
  have hb := relationCount_mono X (graphSelected graphNear) nearAntipodalEdge (by
    intro x hx y hy hs
    norm_num [graphSelected,graphNear,graphs,graphRadial] at hs
    exact ⟨hs.1.1.2,hs.1.2.2,hs.2.2⟩)
  rw [relationCount_eq_sum_card X nearAntipodalEdge] at hb
  exact hb.trans (nearAntipodalEdges_le hX)

theorem graphNarrow_count_le {X : Finset E4} (hX : Admissible X) :
    relationCount X (graphSelected graphNarrow) ≤ 604 := by
  have hb := relationCount_mono X (graphSelected graphNarrow) narrowAntipodalEdge (by
    intro x hx y hy hs
    norm_num [graphSelected,graphNarrow,graphs,graphRadial] at hs
    exact ⟨hs.1.1.1,hs.1.1.2,hs.1.2.1,hs.1.2.2,hs.2.2⟩)
  rw [relationCount_eq_sum_card X narrowAntipodalEdge] at hb
  exact hb.trans (narrowAntipodalEdges_le hX)

theorem graphModerate_count_le {X : Finset E4} (hX : Admissible X) :
    relationCount X (graphSelected graphModerate) ≤ 1880 := by
  have he := relationCount_filter X (graphSelected graphModerate)
    (fun x => 7/5 ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2) (by
      intro x hx y hy hs
      norm_num [graphSelected,graphModerate,graphs,graphRadial] at hs
      exact hs.1)
  rw [← he]
  have hb := relationCount_mono (moderateGraphVertices X) (graphSelected graphModerate)
    (fun x y => -4/5 ≤ ⟪dir x,dir y⟫ ∧ ⟪dir x,dir y⟫ ≤ -11/20) (by
      intro x hx y hy hs
      norm_num [graphSelected,graphModerate,graphs,graphRadial] at hs
      simpa only [neg_div] using hs.2)
  convert hb.trans (moderateGraphEdges_le hX) using 2 <;>
    ext x <;> simp [moderateGraphVertices]

def graphBroad : Graph := graphs[2]

theorem graphBroad_selected {x y : E4} (hx : x ≠ 0) (hy : y ≠ 0) :
    graphSelected graphBroad x y ↔ broadEdge x y := by
  have hp : 0 < ‖x‖*‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  have hl := real_inner_le_norm (-dir x) (dir y)
  simp only [inner_neg_left,norm_neg,norm_dir hx,norm_dir hy,mul_one] at hl
  constructor
  · intro hs
    norm_num [graphSelected,graphBroad,graphs,graphRadial] at hs
    refine ⟨hs.1.1.1,hs.1.1.2,hs.1.2.1,hs.1.2.2,?_⟩
    have ht := hs.2.2
    rw [inner_dir,div_le_iff₀ hp] at ht
    exact ht
  · intro hs
    norm_num [graphSelected,graphBroad,graphs,graphRadial]
    refine ⟨⟨⟨hs.1,hs.2.1⟩,hs.2.2.1,hs.2.2.2.1⟩,by linarith,?_⟩
    rw [inner_dir,div_le_iff₀ hp]
    exact hs.2.2.2.2

theorem graphBroad_count_eq {X : Finset E4} (hX : Admissible X) :
    relationCount X (graphSelected graphBroad) = broadEdges X := by
  have hn : ∀ x ∈ X, x ≠ 0 := by
    intro x hx he
    have h := hX.1 x hx
    norm_num [he] at h
  rw [relationCount_congr X (graphSelected graphBroad) broadEdge
    (fun x hx y hy => graphBroad_selected (hn x hx) (hn y hy)),
    relationCount_eq_sum_card,broadEdges_eq_sum]

theorem graphBroad_energy {X : Finset E4} (hX : Admissible X) :
    graphValue graphBroad X = nbhdEnergy Kg X := by
  rw [graphValue,graphBroad_count_eq hX,nbhdEnergy_Kg hX]
  norm_num [graphBroad,graphs]
  ring

theorem graphValue_nonneg (g : Graph) (X : Finset E4)
    (hw : (0 : ℝ) ≤ (g.weight : ℝ))
    (hc : (relationCount X (graphSelected g) : ℝ) ≤ (g.capacity : ℝ)) :
    0 ≤ graphValue g X := mul_nonneg hw (sub_nonneg.mpr hc)

/-- Removing the broad graph leaves the three other active graph energies,
each nonnegative by its exact geometric edge bound. -/
theorem graphs_residual_nonneg {X : Finset E4} (hX : Admissible X) :
    0 ≤ graphsEnergy X - nbhdEnergy Kg X := by
  have hn := graphValue_nonneg graphNear X (by norm_num [graphNear,graphs])
    (by
      rw [show (graphNear.capacity : ℝ) = 120 by norm_num [graphNear,graphs]]
      exact_mod_cast graphNear_count_le hX)
  have hs := graphValue_nonneg graphNarrow X (by norm_num [graphNarrow,graphs])
    (by
      rw [show (graphNarrow.capacity : ℝ) = 604 by norm_num [graphNarrow,graphs]]
      exact_mod_cast graphNarrow_count_le hX)
  have hm := graphValue_nonneg graphModerate X (by norm_num [graphModerate,graphs])
    (by
      rw [show (graphModerate.capacity : ℝ) = 1880 by norm_num [graphModerate,graphs]]
      exact_mod_cast graphModerate_count_le hX)
  have he : graphsEnergy X = graphValue graphBroad X + graphValue graphNear X +
      graphValue graphNarrow X + graphValue graphModerate X := by
    rw [graphs_energy_identity]
    norm_num [graphs,graphBroad,graphNear,graphNarrow,graphModerate,graphValue]
    ring
  rw [he,graphBroad_energy hX]
  linarith

end
end D4Bound.V7
