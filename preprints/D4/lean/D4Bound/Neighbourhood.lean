import D4Bound.LocalEnergy
import D4Bound.FarPair
import D4Bound.Density
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Neighbourhoods, counts and the broad graph

An *admissible neighbourhood* is a finite set `X ⊆ ℝ⁴` with `‖x‖ ≥ 1` for `x ∈ X` and
`‖x - y‖ ≥ 1` for distinct `x, y ∈ X`: the neighbours of a centre, seen from the centre.
Its anchored energy for a kernel `K` is

  `E_K(X) = K(0,0) + 2 ∑_{x ∈ X} K(x,0) + ∑_{x, y ∈ X} K(x,y)`.

The counts are `n_j = #{x ∈ X : ‖x‖ ≤ R_j}`, `N = n_5`, and the group of `X` is `(N, j)` with
`j` the least index in `1..5` such that `n_j = N`.

`Kg` is the broad graph energy of the base certificate: `δ (1358 - e(X))` with
`δ = 1/50000000`, where `e(X)` counts ordered pairs of neighbours with radii in
`[33/28, 7/4]` and cosine in `[-1, -7/8]`.

`energy_eq_nbhdEnergy` identifies the anchored energy of a centre in a finite family with the
anchored energy of its neighbourhood.
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound

/-! ## Radii -/

/-- `R₁ = 501473/500000`. -/
noncomputable def R1 : ℝ := 501473 / 500000
/-- `R₂ = 1005643/1000000`. -/
noncomputable def R2 : ℝ := 1005643 / 1000000
/-- `R₃ = 50379/50000`. -/
noncomputable def R3 : ℝ := 50379 / 50000
/-- `R₄ = 50767/50000`. -/
noncomputable def R4 : ℝ := 50767 / 50000

lemma R1_le_R5 : R1 ≤ R5 := by norm_num [R1, R5]

/-! ## Neighbourhoods -/

/-- Admissible neighbourhood: all points at norm `≥ 1`, distinct points at distance `≥ 1`. -/
def Admissible (X : Finset E4) : Prop :=
  (∀ x ∈ X, 1 ≤ ‖x‖) ∧ ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ ‖x - y‖

/-- Anchored energy `E_K(X) = K(0,0) + 2 ∑_{x ∈ X} K(x,0) + ∑_{x,y ∈ X} K(x,y)`. -/
noncomputable def nbhdEnergy (K : E4 → E4 → ℝ) (X : Finset E4) : ℝ :=
  K 0 0 + 2 * ∑ x ∈ X, K x 0 + ∑ x ∈ X, ∑ y ∈ X, K x y

open Classical in
/-- `#{x ∈ X : ‖x‖ ≤ r}`. -/
noncomputable def countWithin (X : Finset E4) (r : ℝ) : ℕ := (X.filter fun x => ‖x‖ ≤ r).card

/-- `N = n₅`, the number of near neighbours. -/
noncomputable def nearCount (X : Finset E4) : ℕ := countWithin X R5

/-- The least `j ∈ {1,…,5}` with `n_j = N`. -/
noncomputable def firstRadius (X : Finset E4) : ℕ :=
  if countWithin X R1 = nearCount X then 1
  else if countWithin X R2 = nearCount X then 2
  else if countWithin X R3 = nearCount X then 3
  else if countWithin X R4 = nearCount X then 4
  else 5

/-! ## The broad graph -/

/-- An edge of the broad graph: radii in `[33/28, 7/4]`, cosine at most `-7/8`. -/
def broadEdge (x y : E4) : Prop :=
  33 / 28 ≤ ‖x‖ ∧ ‖x‖ ≤ 7 / 4 ∧ 33 / 28 ≤ ‖y‖ ∧ ‖y‖ ≤ 7 / 4 ∧ ⟪x, y⟫ ≤ -(7 / 8) * (‖x‖ * ‖y‖)

open Classical in
/-- `e(X)`, the number of ordered edges of the broad graph in `X`. -/
noncomputable def broadEdges (X : Finset E4) : ℕ :=
  ((X ×ˢ X).filter fun q => broadEdge q.1 q.2).card

open Classical in
/-- The broad graph energy as a kernel: `δ·1358` at the origin, `-δ` on each edge. -/
noncomputable def Kg (x y : E4) : ℝ :=
  if x = 0 ∧ y = 0 then 1358 / 50000000 else if broadEdge x y then -(1 / 50000000) else 0

lemma not_broadEdge_zero (x : E4) : ¬ broadEdge x 0 := by
  intro h; have := h.2.2.1; simp at this; linarith

lemma nbhdEnergy_Kg {X : Finset E4} (hX : Admissible X) :
    nbhdEnergy Kg X = 1358 / 50000000 - broadEdges X / 50000000 := by
  classical
  have h0 : ∀ x ∈ X, x ≠ 0 := fun x hx h => by
    have := hX.1 x hx; rw [h, norm_zero] at this; linarith
  have hlin : ∑ x ∈ X, Kg x 0 = 0 := Finset.sum_eq_zero fun x hx => by
    simp [Kg, h0 x hx, not_broadEdge_zero]
  have hquad : ∑ x ∈ X, ∑ y ∈ X, Kg x y =
      ∑ q ∈ X ×ˢ X, (if broadEdge q.1 q.2 then -(1 / 50000000 : ℝ) else 0) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    simp [Kg, h0 x hx]
  rw [nbhdEnergy, hlin, hquad, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, broadEdges]
  simp only [Kg, and_self, if_true]
  ring

/-- With at most 1208 edges, the broad graph energy is at least `3/10⁶`. -/
lemma nbhdEnergy_Kg_ge {X : Finset E4} (hX : Admissible X) (he : broadEdges X ≤ 1208) :
    3 / 1000000 ≤ nbhdEnergy Kg X := by
  rw [nbhdEnergy_Kg hX]
  have : (broadEdges X : ℝ) ≤ 1208 := by exact_mod_cast he
  linarith

lemma nbhdEnergy_sub (K L : E4 → E4 → ℝ) (X : Finset E4) :
    nbhdEnergy (fun x y => K x y - L x y) X = nbhdEnergy K X - nbhdEnergy L X := by
  simp only [nbhdEnergy, Finset.sum_sub_distrib]; ring

lemma nbhdEnergy_add (K L : E4 → E4 → ℝ) (X : Finset E4) :
    nbhdEnergy (fun x y => K x y + L x y) X = nbhdEnergy K X + nbhdEnergy L X := by
  simp only [nbhdEnergy, Finset.sum_add_distrib]; ring

/-! ## From a finite family to the neighbourhood of one centre -/

section family

variable {n : ℕ} (p : Fin n → E4)

/-- The family is unit separated. -/
def Separated : Prop := ∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖

/-- The neighbourhood of centre `i`: `{p j - p i : j ≠ i}`. -/
noncomputable def nbhd (i : Fin n) : Finset E4 :=
  (Finset.univ.filter fun j => j ≠ i).image fun j => p j - p i

variable {p}

lemma nbhd_injOn (hp : Separated p) (i : Fin n) :
    Set.InjOn (fun j => p j - p i) (Finset.univ.filter fun j => j ≠ i : Finset (Fin n)) := by
  intro j _ k _ h
  by_contra hjk
  have := hp j k (Ne.symm hjk)
  simp only [sub_left_inj] at h
  rw [h, sub_self, norm_zero] at this
  linarith

lemma nbhd_admissible (hp : Separated p) (i : Fin n) : Admissible (nbhd p i) := by
  constructor
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hp i j (Finset.mem_filter.mp hj).2
  · intro x hx y hy hxy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    have hjk : j ≠ k := fun h => hxy (by rw [h])
    have := hp k j hjk
    rwa [show p j - p i - (p k - p i) = p j - p k by abel]

lemma sum_nbhd (hp : Separated p) (i : Fin n) (φ : E4 → ℝ) :
    ∑ j, (if j ≠ i then φ (p j - p i) else 0) = ∑ x ∈ nbhd p i, φ x := by
  rw [nbhd, Finset.sum_image (nbhd_injOn hp i), Finset.sum_filter]

lemma sum_sum_nbhd (hp : Separated p) (i : Fin n) (φ : E4 → E4 → ℝ) :
    ∑ j, ∑ k, (if j ≠ i ∧ k ≠ i then φ (p j - p i) (p k - p i) else 0) =
      ∑ x ∈ nbhd p i, ∑ y ∈ nbhd p i, φ x y := by
  have h : ∀ j, ∑ k, (if j ≠ i ∧ k ≠ i then φ (p j - p i) (p k - p i) else 0) =
      if j ≠ i then ∑ y ∈ nbhd p i, φ (p j - p i) y else 0 := by
    intro j
    by_cases hj : j ≠ i
    · rw [if_pos hj, ← sum_nbhd hp i (φ (p j - p i))]
      exact Finset.sum_congr rfl fun k _ => by by_cases hk : k = i <;> simp [hj, hk]
    · have hji : j = i := not_not.mp hj
      subst hji
      simp
  simp only [h]
  exact sum_nbhd hp i (fun x => ∑ y ∈ nbhd p i, φ x y)

/-- The anchored energy of centre `i` is the energy of its neighbourhood. -/
lemma energy_eq_nbhdEnergy (hp : Separated p) (K : E4 → E4 → ℝ) (i : Fin n) :
    energy K (K 0 0) p i = nbhdEnergy K (nbhd p i) := by
  rw [energy, nbhdEnergy, sum_nbhd hp i (fun x => K x 0),
    sum_sum_nbhd hp i K]

end family

end D4Bound
