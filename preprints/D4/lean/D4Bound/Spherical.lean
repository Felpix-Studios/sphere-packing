import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# A quartic sum over unit vectors in `ℝ⁴`

For unit vectors `u 0, …, u (n-1)` in `ℝ⁴` with inner products `t i k`, and `a² ≤ 1/2`,

  ∑_{i,k} (t⁴ - a² t²) ≥ (1/8 - a²/4) n².

This is the positive-type bound used by the far-pair lemma. The usual proof writes
`t⁴ - a² t²` in Chebyshev polynomials `U₀, U₂, U₄`, which are positive definite on `S³`.
Here we use an elementary route: with `G = ∑ uᵢ uᵢᵀ` and `T = ∑ uᵢ^{⊗4}`,
`∑ t² = ‖G‖² ≥ n²/4`, and Cauchy–Schwarz against the symmetrized tensor
`P = Sym(G ⊗ δ)` gives `‖T‖² (48 ‖G‖² + 6 n²) ≥ 36 ‖G‖⁴`.
-/

namespace D4Bound

open Finset

/-- The Kronecker delta. -/
def kd (a b : Fin 4) : ℝ := if a = b then 1 else 0

/-- Four-index tensors on `ℝ⁴`. -/
abbrev Idx := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- The symmetrized trace tensor of a matrix. -/
def symTr (g : Fin 4 → Fin 4 → ℝ) (x : Idx) : ℝ :=
  g x.1 x.2.1 * kd x.2.2.1 x.2.2.2 + g x.1 x.2.2.1 * kd x.2.1 x.2.2.2 +
  g x.1 x.2.2.2 * kd x.2.1 x.2.2.1 + kd x.1 x.2.1 * g x.2.2.1 x.2.2.2 +
  kd x.1 x.2.2.1 * g x.2.1 x.2.2.2 + kd x.1 x.2.2.2 * g x.2.1 x.2.2.1

/-- The fourth tensor power of a vector. -/
def pow4 (v : Fin 4 → ℝ) (x : Idx) : ℝ := v x.1 * v x.2.1 * v x.2.2.1 * v x.2.2.2

lemma sum_idx (F : Idx → ℝ) :
    ∑ x, F x = ∑ a, ∑ b, ∑ c, ∑ d, F (a, b, c, d) := by
  simp only [Fintype.sum_prod_type]

lemma pow4_inner (v w : Fin 4 → ℝ) :
    ∑ x, pow4 v x * pow4 w x = (∑ a, v a * w a) ^ 4 := by
  rw [sum_idx]
  simp only [pow4, Fin.sum_univ_four]
  ring

set_option maxRecDepth 100000 in
lemma pow4_symTr (v : Fin 4 → ℝ) (g : Fin 4 → Fin 4 → ℝ) :
    ∑ x, pow4 v x * symTr g x =
      6 * (∑ a, ∑ b, v a * v b * g a b) * (∑ c, v c ^ 2) := by
  rw [sum_idx]
  simp only [Fin.sum_univ_four]
  simp only [pow4, symTr, kd, Fin.isValue, Fin.reduceEq, if_true, if_false, mul_one, mul_zero,
    zero_mul, one_mul, add_zero, zero_add]
  ring

set_option maxRecDepth 100000 in
lemma symTr_sq (g : Fin 4 → Fin 4 → ℝ) (hg : ∀ a b, g a b = g b a) :
    ∑ x, symTr g x ^ 2 = 48 * ∑ a, ∑ b, g a b ^ 2 + 6 * (∑ a, g a a) ^ 2 := by
  rw [sum_idx]
  simp only [Fin.sum_univ_four]
  simp only [symTr, kd, Fin.isValue, Fin.reduceEq, if_true, if_false, mul_one, mul_zero,
    zero_mul, one_mul, add_zero, zero_add]
  rw [hg 1 0, hg 2 0, hg 3 0, hg 2 1, hg 3 1, hg 3 2]
  ring

lemma trace_sq_bound (g : Fin 4 → Fin 4 → ℝ) :
    (∑ a, g a a) ^ 2 ≤ 4 * ∑ a, ∑ b, g a b ^ 2 := by
  simp only [Fin.sum_univ_four]
  nlinarith [sq_nonneg (g 0 0 - g 1 1), sq_nonneg (g 0 0 - g 2 2), sq_nonneg (g 0 0 - g 3 3),
    sq_nonneg (g 1 1 - g 2 2), sq_nonneg (g 1 1 - g 3 3), sq_nonneg (g 2 2 - g 3 3),
    sq_nonneg (g 0 1), sq_nonneg (g 0 2), sq_nonneg (g 0 3), sq_nonneg (g 1 0),
    sq_nonneg (g 1 2), sq_nonneg (g 1 3), sq_nonneg (g 2 0), sq_nonneg (g 2 1),
    sq_nonneg (g 2 3), sq_nonneg (g 3 0), sq_nonneg (g 3 1), sq_nonneg (g 3 2)]

section family

variable {n : ℕ} (u : Fin n → Fin 4 → ℝ)

/-- Inner products. -/
def ip (i k : Fin n) : ℝ := ∑ a, u i a * u k a

/-- The frame matrix `∑ uᵢ uᵢᵀ`. -/
def frame (a b : Fin 4) : ℝ := ∑ i, u i a * u i b

lemma frame_symm (a b : Fin 4) : frame u a b = frame u b a := by
  unfold frame; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma swap4 {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → ι → κ → κ → ℝ) :
    ∑ i, ∑ k, ∑ a, ∑ b, F i k a b = ∑ a, ∑ b, ∑ i, ∑ k, F i k a b := by
  calc ∑ i, ∑ k, ∑ a, ∑ b, F i k a b = ∑ i, ∑ a, ∑ k, ∑ b, F i k a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ k, ∑ b, F i k a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ k, F i k a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ k, F i k a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma ip_sq_expand (i k : Fin n) :
    ip u i k ^ 2 = ∑ a, ∑ b, u i a * u i b * (u k a * u k b) := by
  unfold ip; rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma sum_ip_sq : ∑ i, ∑ k, ip u i k ^ 2 = ∑ a, ∑ b, frame u a b ^ 2 := by
  have h1 := ip_sq_expand u
  have h2 : ∀ a b, frame u a b ^ 2 = ∑ i, ∑ k, u i a * u i b * (u k a * u k b) := by
    intro a b; unfold frame; rw [sq, Finset.sum_mul_sum]
  simp only [h1, h2]
  exact swap4 _

lemma trace_frame (hu : ∀ i, ∑ a, u i a ^ 2 = 1) : ∑ a, frame u a a = n := by
  unfold frame
  rw [Finset.sum_comm]
  simp [← sq, hu]

/-- `∑ t² ≥ n²/4`. -/
lemma sum_ip_sq_ge (hu : ∀ i, ∑ a, u i a ^ 2 = 1) :
    (n : ℝ) ^ 2 ≤ 4 * ∑ i, ∑ k, ip u i k ^ 2 := by
  rw [sum_ip_sq, ← trace_frame u hu]
  exact trace_sq_bound _

/-- The fourth-power tensor of the family. -/
def tens (x : Idx) : ℝ := ∑ i, pow4 (u i) x

lemma tens_sq : ∑ x, tens u x ^ 2 = ∑ i, ∑ k, ip u i k ^ 4 := by
  unfold tens
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow4_inner]; rfl

lemma tens_symTr (hu : ∀ i, ∑ a, u i a ^ 2 = 1) :
    ∑ x, tens u x * symTr (frame u) x = 6 * ∑ i, ∑ k, ip u i k ^ 2 := by
  unfold tens
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [pow4_symTr, hu, mul_one]
  rw [← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ip_sq_expand]
  unfold frame
  simp only [Finset.mul_sum]
  calc ∑ a, ∑ b, ∑ k, u i a * u i b * (u k a * u k b)
      = ∑ a, ∑ k, ∑ b, u i a * u i b * (u k a * u k b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, u i a * u i b * (u k a * u k b) := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, u i a * u i b * (u k a * u k b) := rfl

/-- The Cauchy–Schwarz step: `S₄ (48 S₂ + 6 n²) ≥ 36 S₂²`. -/
lemma quartic_cs (hu : ∀ i, ∑ a, u i a ^ 2 = 1) :
    36 * (∑ i, ∑ k, ip u i k ^ 2) ^ 2 ≤
      (∑ i, ∑ k, ip u i k ^ 4) * (48 * ∑ i, ∑ k, ip u i k ^ 2 + 6 * (n : ℝ) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (tens u) (symTr (frame u))
  rw [tens_symTr u hu, tens_sq, symTr_sq _ (frame_symm u), trace_frame u hu,
    ← sum_ip_sq] at hcs
  nlinarith [hcs]

/-- The quartic bound: `∑_{i,k} (t⁴ - a² t²) ≥ (1/8 - a²/4) n²` for `a² ≤ 1/2`. -/
theorem quartic_sum_ge (hu : ∀ i, ∑ a, u i a ^ 2 = 1) (a2 : ℝ) (_ha0 : 0 ≤ a2)
    (ha : a2 ≤ 1 / 2) :
    (1 / 8 - a2 / 4) * (n : ℝ) ^ 2 ≤ ∑ i, ∑ k, (ip u i k ^ 4 - a2 * ip u i k ^ 2) := by
  have hcs := quartic_cs u hu
  have h2 := sum_ip_sq_ge u hu
  set S2 := ∑ i, ∑ k, ip u i k ^ 2
  set S4 := ∑ i, ∑ k, ip u i k ^ 4
  have hsplit : ∑ i, ∑ k, (ip u i k ^ 4 - a2 * ip u i k ^ 2) = S4 - a2 * S2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [hsplit]
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hD : 0 < 48 * S2 + 6 * (n : ℝ) ^ 2 + 1 := by nlinarith
  -- (S4 - a2 S2 - c n²) D ≥ 6 (S2 - n²/4) ((6 - 8 a2) S2 + (1/2 - a2) n²) ≥ 0
  have hkey : 0 ≤ (S4 - a2 * S2 - (1 / 8 - a2 / 4) * (n : ℝ) ^ 2) *
      (48 * S2 + 6 * (n : ℝ) ^ 2) := by
    have hf : 0 ≤ (4 * S2 - (n : ℝ) ^ 2) * ((6 - 8 * a2) * S2 + (1 / 2 - a2) * (n : ℝ) ^ 2) := by
      apply mul_nonneg
      · linarith
      · have : 0 ≤ S2 := by nlinarith
        nlinarith
    nlinarith [hf, hcs]
  by_contra hlt0
  have hlt := not_le.mp hlt0
  have hpos : 0 < 48 * S2 + 6 * (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exfalso
      have hS : S4 - a2 * S2 = 0 := by simp [S4, S2]
      have h0' : (1 / 8 - a2 / 4) * ((0 : ℕ) : ℝ) ^ 2 = 0 := by simp
      linarith
    · have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      nlinarith
  nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos]

/-- Off the diagonal: `∑_{i ≠ k} (t⁴ - a² t²) ≥ (1/8 - a²/4) n² - (1 - a²) n`. -/
theorem quartic_offdiag_ge (hu : ∀ i, ∑ a, u i a ^ 2 = 1) (a2 : ℝ) (ha0 : 0 ≤ a2)
    (ha : a2 ≤ 1 / 2) :
    (1 / 8 - a2 / 4) * (n : ℝ) ^ 2 - (1 - a2) * n ≤
      ∑ i, ∑ k, (if k ≠ i then ip u i k ^ 4 - a2 * ip u i k ^ 2 else 0) := by
  have h := quartic_sum_ge u hu a2 ha0 ha
  have hdiag : ∀ i, ∑ k, (ip u i k ^ 4 - a2 * ip u i k ^ 2) =
      (1 - a2) + ∑ k, (if k ≠ i then ip u i k ^ 4 - a2 * ip u i k ^ 2 else 0) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hii : ip u i i = 1 := by unfold ip; simpa [sq] using hu i
    simp only [hii, ne_eq, not_true_eq_false, if_false]
    have : ∑ k ∈ univ.erase i, (if ¬k = i then ip u i k ^ 4 - a2 * ip u i k ^ 2 else 0) =
        ∑ k ∈ univ.erase i, (ip u i k ^ 4 - a2 * ip u i k ^ 2) :=
      Finset.sum_congr rfl fun k hk => by simp [Finset.ne_of_mem_erase hk]
    rw [this]; ring
  simp only [hdiag, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  linarith

end family

end D4Bound
