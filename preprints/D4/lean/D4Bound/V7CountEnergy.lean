import D4Bound.V7Energy

/-! Concrete count kernels evaluate to the count polynomials used by the census. -/
open Finset
namespace D4Bound.V7
noncomputable section
open Classical

theorem sum_list_map {α : Type*} (L : List α) (X : Finset E4) (g : α → E4 → ℝ) :
    (∑ x ∈ X, (L.map fun a => g a x).sum) =
      (L.map fun a => ∑ x ∈ X, g a x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem indicator_sum (X : Finset E4) (R : ℚ) :
    (∑ x ∈ X, indicator R ‖x‖) = (countWithin X (R : ℝ) : ℝ) := by
  simp [indicator, countWithin]

theorem list_bilinear_sum (I J : List ℕ) (X : Finset E4)
    (a : ℕ → ℕ → ℝ) (u : ℕ → E4 → ℝ) :
    (∑ x ∈ X, ∑ y ∈ X,
      (I.map fun i => (J.map fun j => a i j * u i x * u j y).sum).sum) =
      (I.map fun i => (J.map fun j =>
        a i j * (∑ x ∈ X, u i x) * (∑ y ∈ X, u j y)).sum).sum := by
  induction I with
  | nil => simp
  | cons i I ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    clear ih
    congr 1
    induction J with
    | nil => simp
    | cons j J hj =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, hj]
      congr 1
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

def countValue (c : CountPolynomial) (X : Finset E4) : ℝ :=
  let n := fun i => (countWithin X ((c.radii.getD i 0 : ℚ) : ℝ) : ℝ)
  (c.weight : ℝ) * ((c.constant : ℝ) +
    2 * ((List.range c.radii.length).map fun i => ((c.linear.getD i 0 : ℚ) : ℝ)*n i).sum +
    ((List.range c.radii.length).map fun i => ((List.range c.radii.length).map fun j =>
      (((c.matrix.getD i []).getD j 0 : ℚ) : ℝ)*n i*n j).sum).sum)

theorem count_linear_sum (c : CountPolynomial) (X : Finset E4) :
    (∑ x ∈ X, countLinear c ‖x‖) = (c.weight : ℝ) *
      ((List.range c.radii.length).map fun i => ((c.linear.getD i 0 : ℚ) : ℝ) *
        (countWithin X ((c.radii.getD i 0 : ℚ) : ℝ) : ℝ)).sum := by
  unfold countLinear
  rw [← Finset.mul_sum, sum_list_map]
  simp_rw [← Finset.mul_sum, indicator_sum]

theorem count_pair_sum (c : CountPolynomial) (X : Finset E4) :
    (∑ x ∈ X, ∑ y ∈ X, countPair c ‖x‖ ‖y‖) = (c.weight : ℝ) *
      ((List.range c.radii.length).map fun i => ((List.range c.radii.length).map fun j =>
        (((c.matrix.getD i []).getD j 0 : ℚ) : ℝ) *
          (countWithin X ((c.radii.getD i 0 : ℚ) : ℝ) : ℝ) *
          (countWithin X ((c.radii.getD j 0 : ℚ) : ℝ) : ℝ)).sum).sum := by
  unfold countPair
  simp_rw [← Finset.mul_sum]
  rw [list_bilinear_sum]
  simp_rw [indicator_sum]

theorem count_component_identity (c : CountPolynomial) (X : Finset E4) :
    radialEnergy ((c.weight*c.constant : ℚ) : ℝ) (countLinear c)
      (fun r s _ => countPair c r s) X = countValue c X := by
  unfold radialEnergy
  rw [count_linear_sum, count_pair_sum]
  unfold countValue
  push_cast
  ring

theorem radialEnergy_list {α : Type*} (L : List α) (A : α → ℝ)
    (h : α → ℝ → ℝ) (k : α → ℝ → ℝ → ℝ → ℝ) (X : Finset E4) :
    radialEnergy (L.map A).sum (fun r => (L.map fun c => h c r).sum)
      (fun r s t => (L.map fun c => k c r s t).sum) X =
      (L.map fun c => radialEnergy (A c) (h c) (k c) X).sum := by
  induction L with
  | nil => simp [radialEnergy]
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons]
    unfold radialEnergy at ih ⊢
    simp only [Finset.sum_add_distrib]
    rw [← ih]
    ring

theorem rat_sum_cast (L : List ℚ) : ((L.sum : ℚ) : ℝ) = (L.map fun q => (q : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [ih]

theorem count_origin_cast (L : List CountPolynomial) :
    (((L.map fun c => c.weight*c.constant).sum : ℚ) : ℝ) =
      (L.map fun c => ((c.weight*c.constant : ℚ) : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons c L ih => simp [ih]

/-- All three actual count components, with their constants, weights and multiplicities. -/
theorem counts_energy_identity (X : Finset E4) :
    countsEnergy X = (countPolynomials.map fun c => countValue c X).sum := by
  unfold countsEnergy countOriginQ countsLinear countsPair
  rw [count_origin_cast]
  rw [radialEnergy_list]
  simp_rw [count_component_identity]

end
end D4Bound.V7
