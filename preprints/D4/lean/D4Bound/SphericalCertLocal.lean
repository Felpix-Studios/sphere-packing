import D4Bound.LocalEnergy

/-! The anchored-energy summation identity for spherical certificate kernels.
The kernel may depend on three indices; no translation invariance is assumed. -/
namespace D4Bound
namespace SphereLocal

open Finset



/-- Anchored energy of centre `i`. -/
noncomputable def energy {n : ℕ} (K : Fin n → Fin n → Fin n → ℝ) (v : Fin n → Fin n → ℝ) (A : ℝ) (i : Fin n) : ℝ :=
  A + 2 * ∑ j, (if j ≠ i then v i j else 0)
    + ∑ j, ∑ k, (if j ≠ i ∧ k ≠ i then K i j k else 0)

/-- Triangle sum of the kernel at the three anchors of a triangle. -/
def gamma {n : ℕ} (K : Fin n → Fin n → Fin n → ℝ) (i j k : Fin n) : ℝ :=
  K i j k + K j i k + K k i j

/-- Sum over ordered triples of distinct indices of the kernel anchored at the first. -/
noncomputable def tripleSum {n : ℕ} (K : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, (if j ≠ i ∧ k ≠ i ∧ k ≠ j then K i j k else 0)

lemma sum_swap12 {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ j, ∑ k, F j i k := Finset.sum_comm

lemma sum_swap13 {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ j, ∑ k, F k j i := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- Three copies of the triple sum are the sum of the triangle sums. -/
lemma three_tripleSum {n : ℕ} (K : Fin n → Fin n → Fin n → ℝ) :
    3 * tripleSum K =
      ∑ i, ∑ j, ∑ k, (if j ≠ i ∧ k ≠ i ∧ k ≠ j then gamma K i j k else 0) := by
  have h2 : (∑ i, ∑ j, ∑ k,
      (if j ≠ i ∧ k ≠ i ∧ k ≠ j then K j i k else 0)) = tripleSum K := by
    rw [sum_swap12]
    unfold tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    refine if_congr ?_ rfl rfl
    exact ⟨fun h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩, fun h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  have h3 : (∑ i, ∑ j, ∑ k,
      (if j ≠ i ∧ k ≠ i ∧ k ≠ j then K k i j else 0)) = tripleSum K := by
    rw [sum_swap13]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    unfold tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    refine if_congr ?_ rfl rfl
    exact ⟨fun h => ⟨h.2.1.symm, h.2.2.symm, h.1⟩, fun h => ⟨h.2.2, h.1.symm, h.2.1.symm⟩⟩
  have hsplit : (∑ i, ∑ j, ∑ k,
      (if j ≠ i ∧ k ≠ i ∧ k ≠ j then gamma K i j k else 0)) =
      tripleSum K
      + (∑ i, ∑ j, ∑ k,
          (if j ≠ i ∧ k ≠ i ∧ k ≠ j then K j i k else 0))
      + (∑ i, ∑ j, ∑ k,
          (if j ≠ i ∧ k ≠ i ∧ k ≠ j then K k i j else 0)) := by
    unfold tripleSum
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    unfold gamma
    split_ifs <;> ring
  rw [hsplit, h2, h3]
  ring

/-- Separate the diagonal `k = j` from the anchored double sum. -/
lemma split_diag {n : ℕ} (i j : Fin n) (X : Fin n → ℝ) :
    ∑ k, (if j ≠ i ∧ k ≠ i then X k else 0) =
      (if j ≠ i then X j else 0) + ∑ k, (if j ≠ i ∧ k ≠ i ∧ k ≠ j then X k else 0) := by
  have h : ∀ k, (if j ≠ i ∧ k ≠ i then X k else 0) =
      (if j = k then (if j ≠ i then X j else 0) else 0) +
        (if j ≠ i ∧ k ≠ i ∧ k ≠ j then X k else 0) := by
    intro k
    by_cases hk : j = k
    · subst hk; by_cases hji : j = i <;> simp [hji]
    · have hk' : k ≠ j := fun e => hk e.symm
      simp [hk, hk']
  rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

/-- Grouping: the sum of all anchored energies. -/
lemma sum_energy {n : ℕ} (K : Fin n → Fin n → Fin n → ℝ) (v : Fin n → Fin n → ℝ) (A : ℝ) :
    ∑ i, energy K v A i =
      n * A + ∑ i, ∑ j, (if j ≠ i then 2 * v i j + K i j j else 0)
        + tripleSum K := by
  have hE : ∀ i, energy K v A i = A + 2 * ∑ j, (if j ≠ i then v i j else 0)
      + ∑ j, (if j ≠ i then K i j j else 0)
      + ∑ j, ∑ k, (if j ≠ i ∧ k ≠ i ∧ k ≠ j then K i j k else 0) := by
    intro i
    unfold energy
    rw [Finset.sum_congr rfl fun j _ => split_diag i j (fun k => K i j k),
      Finset.sum_add_distrib]
    ring
  have hP : ∀ i, ∑ j, (if j ≠ i then 2 * v i j + K i j j else 0) =
      2 * ∑ j, (if j ≠ i then v i j else 0)
      + ∑ j, (if j ≠ i then K i j j else 0) := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => hE i, Finset.sum_congr rfl fun i _ => hP i]
  unfold tripleSum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- The finite local-energy inequality, with the triple sum assumed nonpositive. -/
theorem finite_local_energy_of_tripleSum {n : ℕ} (f : Fin n → Fin n → ℝ) (K : Fin n → Fin n → Fin n → ℝ)
    (v : Fin n → Fin n → ℝ) (A β B : ℝ) (hdiag : ∀ i, f i i = B)
    (hpair : ∀ i j, j ≠ i → f i j + 2 * v i j + K i j j ≤ 0)
    (hT : tripleSum K ≤ 0)
    (hfloor : ∀ i, β ≤ energy K v A i) :
    ∑ i, ∑ j, f i j ≤ n * (B + A - β) := by
  -- the energy sum
  have hE : (n : ℝ) * β ≤ ∑ i, energy K v A i := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => hfloor i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  rw [sum_energy] at hE
  -- split the diagonal of the scalar sum
  have hf : ∀ i : Fin n, ∑ j, f i j =
      B + ∑ j, (if j ≠ i then f i j else 0) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [hdiag, ne_eq, not_true_eq_false, if_false, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [Finset.ne_of_mem_erase hj]
  simp only [hf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  -- pair terms
  have hp : ∑ i, ∑ j, (if j ≠ i then f i j else 0) ≤
      -∑ i, ∑ j, (if j ≠ i then 2 * v i j + K i j j else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro j _
    split_ifs with h
    · linarith [hpair i j h]
    · simp
  linarith

/-- The finite local-energy inequality: pair signs, triangle signs and an energy floor. -/
theorem finite_local_energy {n : ℕ} (f : Fin n → Fin n → ℝ) (K : Fin n → Fin n → Fin n → ℝ)
    (v : Fin n → Fin n → ℝ) (A β B : ℝ) (hdiag : ∀ i, f i i = B)
    (hpair : ∀ i j, j ≠ i → f i j + 2 * v i j + K i j j ≤ 0)
    (hgamma : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → gamma K i j k ≤ 0)
    (hfloor : ∀ i, β ≤ energy K v A i) :
    ∑ i, ∑ j, f i j ≤ n * (B + A - β) := by
  refine finite_local_energy_of_tripleSum f K v A β B hdiag hpair ?_ hfloor
  have h := three_tripleSum K
  have hle : (∑ i, ∑ j, ∑ k,
      (if j ≠ i ∧ k ≠ i ∧ k ≠ j then gamma K i j k else 0)) ≤ 0 := by
    apply Finset.sum_nonpos; intro i _
    apply Finset.sum_nonpos; intro j _
    apply Finset.sum_nonpos; intro k _
    split_ifs with hc
    · exact hgamma i j k hc.1 hc.2.1 hc.2.2
    · exact le_rfl
  linarith

end SphereLocal
end D4Bound
