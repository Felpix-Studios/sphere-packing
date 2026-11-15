import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Schoenberg's theorem on `S³` for Chebyshev polynomials of the second kind

For every `l`, every finite family of unit vectors `x i ∈ ℝ⁴` and real `c i`,

  `∑_{i,j} c i c j U_l(⟪x i, x j⟫) ≥ 0`,

with `U_l` the Chebyshev polynomial of the second kind (`Polynomial.Chebyshev.U ℝ l`).
This is the case `S³` of I. J. Schoenberg, "Positive definite functions on spheres",
Duke Math. J. 9 (1942) 96-108; `U_l` is the Gegenbauer polynomial of parameter `1`.

## Proof

Work with polynomials in four variables and the Fischer inner product
`[p, q] = ∑_α α! p_α q_α`, which is positive semidefinite. Multiplication by `X i` is adjoint to
`∂ᵢ`, so multiplication by `S = ∑ Xᵢ²` is adjoint to the Laplacian `Δ`, and
`[p, ⟪y, X⟫ˡ] = l! p(y)` for `p` homogeneous of degree `l` (Euler's identity).

For `x ∈ ℝ⁴` let `Zₗ(x)` be the polynomial in `X` given by `Z₀ = 1`, `Z₁ = 2⟪x, X⟫` and
`Z_{l+2} = 2⟪x, X⟫ Z_{l+1} - |x|² S Zₗ`. So `Zₗ(x)(y) = U_l(⟪x, y⟫)` for unit `x`, `y`.
Each `Zₗ(x)` is harmonic, and `Zₗ(y) = 2ˡ ⟪y, X⟫ˡ + S R`. Hence

  `[Zₗ(x), Zₗ(y)] = 2ˡ l! Zₗ(x)(y)`,

and `∑ c i c j Zₗ(x i)(x j) = [∑ c i Zₗ(x i), ∑ c j Zₗ(x j)] / (2ˡ l!) ≥ 0`.
The proof needs no integration over the sphere and no harmonic basis.
-/

open MvPolynomial Finset
open scoped RealInnerProductSpace

namespace D4Bound
namespace Schoenberg

/-- Polynomials in four real variables. -/
abbrev P4 := MvPolynomial (Fin 4) ℝ

/-! ## The Fischer inner product -/

/-- `α! = ∏ⱼ (α j)!` as a real number. -/
noncomputable def wt (α : Fin 4 →₀ ℕ) : ℝ := ∏ j, ((α j).factorial : ℝ)

lemma wt_pos (α : Fin 4 →₀ ℕ) : 0 < wt α :=
  Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _

lemma wt_zero : wt 0 = 1 := by simp [wt]

lemma wt_sub_single (α : Fin 4 →₀ ℕ) (i : Fin 4) (h : α i ≠ 0) :
    wt α = (α i : ℝ) * wt (α - Finsupp.single i 1) := by
  have hj : ∀ j, ((α j).factorial : ℝ) =
      (if j = i then (α i : ℝ) else 1) *
        ((((α - Finsupp.single i 1 : Fin 4 →₀ ℕ)) j).factorial : ℝ) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [if_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      rw [← Nat.cast_mul, Nat.mul_factorial_pred h]
    · simp [hji]
  unfold wt
  rw [Finset.prod_congr rfl (fun j _ => hj j), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i]
  simp

/-- The Fischer inner product `[p, q] = ∑_α α! p_α q_α`. -/
noncomputable def fischer (p q : P4) : ℝ :=
  ∑ α ∈ p.support, wt α * coeff α p * coeff α q

lemma fischer_eq_sum {p : P4} (q : P4) {s : Finset (Fin 4 →₀ ℕ)} (h : p.support ⊆ s) :
    fischer p q = ∑ α ∈ s, wt α * coeff α p * coeff α q := by
  refine Finset.sum_subset h fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.mp hα]
  ring

lemma fischer_add_left (p p' q : P4) :
    fischer (p + p') q = fischer p q + fischer p' q := by
  classical
  set s := p.support ∪ p'.support
  rw [fischer_eq_sum q (s := s) ((MvPolynomial.support_add).trans subset_rfl),
    fischer_eq_sum q (s := s) Finset.subset_union_left,
    fischer_eq_sum q (s := s) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add]
  ring

lemma fischer_C_mul_left (c : ℝ) (p q : P4) :
    fischer (C c * p) q = c * fischer p q := by
  classical
  set s := p.support ∪ (C c * p).support
  rw [fischer_eq_sum q (s := s) Finset.subset_union_right,
    fischer_eq_sum q (s := s) Finset.subset_union_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_C_mul]
  ring

lemma fischer_zero_left (q : P4) : fischer 0 q = 0 := by simp [fischer]

lemma fischer_sum_left {ι : Type*} (s : Finset ι) (p : ι → P4) (q : P4) :
    fischer (∑ i ∈ s, p i) q = ∑ i ∈ s, fischer (p i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fischer_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

lemma fischer_add_right (p q q' : P4) :
    fischer p (q + q') = fischer p q + fischer p q' := by
  unfold fischer
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add]
  ring

lemma fischer_C_mul_right (c : ℝ) (p q : P4) :
    fischer p (C c * q) = c * fischer p q := by
  unfold fischer
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_C_mul]
  ring

lemma fischer_sum_right {ι : Type*} (s : Finset ι) (p : P4) (q : ι → P4) :
    fischer p (∑ i ∈ s, q i) = ∑ i ∈ s, fischer p (q i) := by
  unfold fischer
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sum, Finset.mul_sum]

lemma fischer_zero_right (p : P4) : fischer p 0 = 0 := by simp [fischer]

lemma fischer_self_nonneg (p : P4) : 0 ≤ fischer p p :=
  Finset.sum_nonneg fun α _ => by
    rw [mul_assoc]
    exact mul_nonneg (wt_pos α).le (mul_self_nonneg _)

lemma fischer_monomial_left (α : Fin 4 →₀ ℕ) (a : ℝ) (q : P4) :
    fischer (monomial α a) q = wt α * a * coeff α q := by
  classical
  rw [fischer_eq_sum q (s := {α}) (support_monomial_subset), Finset.sum_singleton,
    coeff_monomial, if_pos rfl]

/-- Multiplication by `X i` is adjoint to `∂ᵢ`. -/
lemma fischer_pderiv_left (i : Fin 4) (p q : P4) :
    fischer (pderiv i p) q = fischer p (X i * q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, fischer_add_left, fischer_add_left, hp, hp']
  | monomial α a =>
    rw [pderiv_monomial, fischer_monomial_left, fischer_monomial_left, coeff_X_mul']
    by_cases h : α i = 0
    · have : i ∉ α.support := by simpa using h
      simp [h, this]
    · have : i ∈ α.support := by simpa using h
      rw [if_pos this, wt_sub_single α i h]
      ring

/-! ## Polynomial operators -/

/-- The linear form `⟪x, X⟫`. -/
noncomputable def lin (x : Fin 4 → ℝ) : P4 := ∑ i, C (x i) * X i

/-- `S = ∑ Xᵢ²`. -/
noncomputable def sq : P4 := ∑ i, X i ^ 2

/-- `|x|²`. -/
def nsq (x : Fin 4 → ℝ) : ℝ := ∑ i, x i ^ 2

/-- Directional derivative `∑ xᵢ ∂ᵢ`. -/
noncomputable def dir (x : Fin 4 → ℝ) (p : P4) : P4 := ∑ i, C (x i) * pderiv i p

/-- Laplacian. -/
noncomputable def lap (p : P4) : P4 := ∑ i, pderiv i (pderiv i p)

/-- `∑ ∂ᵢ p ∂ᵢ q`. -/
noncomputable def gdot (p q : P4) : P4 := ∑ i, pderiv i p * pderiv i q

/-- Euler operator `∑ Xᵢ ∂ᵢ`. -/
noncomputable def euler (p : P4) : P4 := ∑ i, X i * pderiv i p

lemma pderiv_lin (x : Fin 4 → ℝ) (i : Fin 4) : pderiv i (lin x) = C (x i) := by
  classical
  simp [lin, map_sum, pderiv_X, Pi.single_apply]

lemma pderiv_sq (i : Fin 4) : pderiv i sq = C 2 * X i := by
  classical
  simp only [sq, map_sum, pderiv_pow, pderiv_X, Pi.single_apply]
  simp [Finset.sum_ite_eq', map_ofNat]

lemma dir_mul (x : Fin 4 → ℝ) (p q : P4) : dir x (p * q) = dir x p * q + p * dir x q := by
  simp only [dir, pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

lemma dir_add (x : Fin 4 → ℝ) (p q : P4) : dir x (p + q) = dir x p + dir x q := by
  simp only [dir, map_add, mul_add, Finset.sum_add_distrib]

lemma dir_sub (x : Fin 4 → ℝ) (p q : P4) : dir x (p - q) = dir x p - dir x q := by
  simp only [dir, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma dir_C (x : Fin 4 → ℝ) (c : ℝ) : dir x (C c) = 0 := by simp [dir]

lemma dir_lin (x : Fin 4 → ℝ) : dir x (lin x) = C (nsq x) := by
  simp only [dir, pderiv_lin, nsq, map_sum, map_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dir_sq (x : Fin 4 → ℝ) : dir x sq = C 2 * lin x := by
  simp only [dir, pderiv_sq, lin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma lap_add (p q : P4) : lap (p + q) = lap p + lap q := by
  simp only [lap, map_add, Finset.sum_add_distrib]

lemma lap_sub (p q : P4) : lap (p - q) = lap p - lap q := by
  simp only [lap, map_sub, Finset.sum_sub_distrib]

lemma lap_mul (p q : P4) : lap (p * q) = lap p * q + p * lap q + 2 * gdot p q := by
  have h : ∀ i, pderiv i (pderiv i (p * q)) = pderiv i (pderiv i p) * q +
      p * pderiv i (pderiv i q) + 2 * (pderiv i p * pderiv i q) := by
    intro i
    rw [pderiv_mul, map_add, pderiv_mul, pderiv_mul]
    ring
  unfold lap gdot
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]

lemma lap_C (c : ℝ) : lap (C c) = 0 := by simp [lap]

lemma gdot_C (c : ℝ) (q : P4) : gdot (C c) q = 0 := by simp [gdot]

lemma lap_lin (x : Fin 4 → ℝ) : lap (lin x) = 0 := by
  simp only [lap, pderiv_lin, pderiv_C, Finset.sum_const_zero]

lemma lap_sq : lap sq = C 8 := by
  simp only [lap, pderiv_sq, pderiv_C_mul, pderiv_X_self, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← map_nsmul]
  norm_num

lemma gdot_C_mul (c : ℝ) (p q : P4) : gdot (C c * p) q = C c * gdot p q := by
  simp only [gdot, pderiv_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dir_one (x : Fin 4 → ℝ) : dir x 1 = 0 := by rw [← C_1, dir_C]

lemma gdot_lin (x : Fin 4 → ℝ) (q : P4) : gdot (lin x) q = dir x q := by
  simp [gdot, dir, pderiv_lin]

lemma gdot_sq (q : P4) : gdot sq q = C 2 * euler q := by
  simp only [gdot, euler, pderiv_sq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_mul (p q : P4) : euler (p * q) = euler p * q + p * euler q := by
  simp only [euler, pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_sub (p q : P4) : euler (p - q) = euler p - euler q := by
  simp only [euler, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma euler_C (c : ℝ) : euler (C c) = 0 := by simp [euler]

lemma euler_lin (x : Fin 4 → ℝ) : euler (lin x) = lin x := by
  simp only [euler, pderiv_lin]
  unfold lin
  exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_sq : euler sq = C 2 * sq := by
  simp only [euler, pderiv_sq]
  unfold sq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Zonal polynomials -/

/-- `Z₀ = 1`, `Z₁ = 2⟪x,X⟫`, `Z_{l+2} = 2⟪x,X⟫ Z_{l+1} - |x|² S Zₗ`. -/
noncomputable def zonal (x : Fin 4 → ℝ) : ℕ → P4
  | 0 => 1
  | 1 => C 2 * lin x
  | (l + 2) => C 2 * lin x * zonal x (l + 1) - C (nsq x) * sq * zonal x l

lemma zonal_add_two (x : Fin 4 → ℝ) (l : ℕ) :
    zonal x (l + 2) = C 2 * lin x * zonal x (l + 1) - C (nsq x) * sq * zonal x l := rfl

lemma euler_zonal (x : Fin 4 → ℝ) : ∀ l, euler (zonal x l) = C (l : ℝ) * zonal x l
  | 0 => by
    show euler 1 = C ((0 : ℕ) : ℝ) * 1
    rw [← C_1, euler_C]
    simp
  | 1 => by
    show euler (C 2 * lin x) = C ((1 : ℕ) : ℝ) * (C 2 * lin x)
    rw [euler_mul, euler_C, euler_lin]
    simp
  | (l + 2) => by
    rw [zonal_add_two, euler_sub, euler_mul, euler_mul, euler_mul, euler_mul, euler_C, euler_C,
      euler_lin, euler_sq, euler_zonal x (l + 1), euler_zonal x l]
    push_cast
    simp only [map_add, map_natCast, map_ofNat, map_one]
    ring

lemma dir_zonal (x : Fin 4 → ℝ) :
    ∀ l, dir x (zonal x (l + 1)) = C (((l : ℝ) + 2) * nsq x) * zonal x l
  | 0 => by
    show dir x (C 2 * lin x) = C ((((0 : ℕ) : ℝ) + 2) * nsq x) * 1
    rw [dir_mul, dir_C, dir_lin]
    simp only [map_mul, map_add, map_ofNat, Nat.cast_zero, map_zero]
    ring
  | 1 => by
    rw [zonal_add_two, dir_sub, dir_mul, dir_mul, dir_mul, dir_mul, dir_C, dir_C, dir_lin,
      dir_sq, dir_zonal x 0]
    show _ = C ((((1 : ℕ) : ℝ) + 2) * nsq x) * (C 2 * lin x)
    simp only [zonal, dir_one]
    simp only [map_mul, map_add, map_ofNat, map_one, Nat.cast_zero, Nat.cast_one,
      map_zero]
    ring
  | (l + 2) => by
    have h1 := dir_zonal x (l + 1)
    have h0 := dir_zonal x l
    rw [zonal_add_two x (l + 1), dir_sub, dir_mul, dir_mul, dir_mul, dir_mul, dir_C, dir_C,
      dir_lin, dir_sq, h1, h0, zonal_add_two x l]
    push_cast
    simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
    ring

lemma lap_zonal (x : Fin 4 → ℝ) : ∀ l, lap (zonal x l) = 0
  | 0 => by
    show lap 1 = 0
    rw [← C_1, lap_C]
  | 1 => by
    show lap (C 2 * lin x) = 0
    rw [lap_mul, lap_C, lap_lin, gdot_C]
    ring
  | (l + 2) => by
    rw [zonal_add_two, lap_sub, lap_mul, lap_mul, lap_mul, lap_mul, lap_C, lap_C, lap_lin,
      lap_sq, lap_zonal x (l + 1), lap_zonal x l, gdot_C, gdot_C, gdot_C_mul, gdot_C_mul,
      gdot_lin, gdot_sq, dir_zonal x l, euler_zonal x l]
    simp only [map_mul, map_add, map_natCast, map_ofNat]
    ring

lemma zonal_isHomogeneous (x : Fin 4 → ℝ) : ∀ l, (zonal x l).IsHomogeneous l
  | 0 => by simpa [zonal] using isHomogeneous_one (Fin 4) ℝ
  | 1 => by
    have hl : (lin x).IsHomogeneous 1 := by
      refine IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (isHomogeneous_C (Fin 4) (x i)).mul (isHomogeneous_X ℝ i)
    simpa [zonal] using (isHomogeneous_C (Fin 4) (2 : ℝ)).mul hl
  | (l + 2) => by
    have hl : (lin x).IsHomogeneous 1 := by
      refine IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (isHomogeneous_C (Fin 4) (x i)).mul (isHomogeneous_X ℝ i)
    have hs : (sq : P4).IsHomogeneous 2 := by
      refine IsHomogeneous.sum _ _ _ fun i _ => ?_
      exact (isHomogeneous_X ℝ i).pow 2
    have ha : (C 2 * lin x * zonal x (l + 1)).IsHomogeneous (l + 2) := by
      have := ((isHomogeneous_C (Fin 4) (2 : ℝ)).mul hl).mul (zonal_isHomogeneous x (l + 1))
      convert this using 1
      ring
    have hb : (C (nsq x) * sq * zonal x l).IsHomogeneous (l + 2) := by
      have := ((isHomogeneous_C (Fin 4) (nsq x)).mul hs).mul (zonal_isHomogeneous x l)
      convert this using 1
      ring
    rw [zonal_add_two]
    exact (homogeneousSubmodule (Fin 4) ℝ (l + 2)).sub_mem ha hb

/-- `Z_l(y) = 2ˡ ⟪y,X⟫ˡ + S R`. -/
lemma zonal_decomp (y : Fin 4 → ℝ) :
    ∀ l, ∃ R : P4, zonal y l = C ((2 : ℝ) ^ l) * lin y ^ l + sq * R
  | 0 => ⟨0, by simp [zonal]⟩
  | 1 => ⟨0, by simp [zonal]⟩
  | (l + 2) => by
    obtain ⟨R1, h1⟩ := zonal_decomp y (l + 1)
    obtain ⟨R0, h0⟩ := zonal_decomp y l
    refine ⟨C 2 * lin y * R1 - C (nsq y) * zonal y l, ?_⟩
    rw [zonal_add_two, h1]
    simp only [map_pow, map_ofNat]
    ring

/-! ## The reproducing identity -/

lemma fischer_mul_lin (y : Fin 4 → ℝ) (p q : P4) :
    fischer p (lin y * q) = fischer (dir y p) q := by
  simp only [lin, dir, Finset.sum_mul, fischer_sum_right, fischer_sum_left, mul_assoc,
    fischer_C_mul_right, fischer_C_mul_left, fischer_pderiv_left]

lemma fischer_mul_sq (p q : P4) : fischer p (sq * q) = fischer (lap p) q := by
  simp only [sq, lap, Finset.sum_mul, fischer_sum_right, fischer_sum_left, pow_two, mul_assoc,
    fischer_pderiv_left]

lemma eval_dir (y : Fin 4 → ℝ) (p : P4) : eval y (dir y p) = eval y (euler p) := by
  simp [dir, euler]

lemma fischer_lin_pow (y : Fin 4 → ℝ) :
    ∀ l (p : P4), p.IsHomogeneous l → fischer p (lin y ^ l) = l.factorial * eval y p
  | 0, p, hp => by
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, pow_zero, ← C_1, ← monomial_zero', fischer_monomial_left]
    simp [wt_zero]
  | (l + 1), p, hp => by
    have hd : (dir y p).IsHomogeneous l := by
      refine IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (isHomogeneous_C (Fin 4) (y i)).mul (hp.pderiv (i := i))
    rw [pow_succ', fischer_mul_lin, fischer_lin_pow y l _ hd, eval_dir, euler,
      hp.sum_X_mul_pderiv]
    simp [Nat.factorial_succ]
    ring

/-- `[Zₗ(x), Zₗ(y)] = 2ˡ l! Zₗ(x)(y)`. -/
lemma fischer_zonal (x y : Fin 4 → ℝ) (l : ℕ) :
    fischer (zonal x l) (zonal y l) = (2 : ℝ) ^ l * l.factorial * eval y (zonal x l) := by
  obtain ⟨R, hR⟩ := zonal_decomp y l
  rw [hR, fischer_add_right, fischer_C_mul_right, fischer_mul_sq, lap_zonal,
    fischer_zero_left, fischer_lin_pow y l _ (zonal_isHomogeneous x l)]
  ring

/-- Positive definiteness of the solid zonal kernel `Zₗ(x)(y)` on all of `ℝ⁴`. -/
theorem zonal_posDef {ι : Type*} (s : Finset ι) (x : ι → Fin 4 → ℝ) (c : ι → ℝ) (l : ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * eval (x j) (zonal (x i) l) := by
  have hk : (0 : ℝ) < (2 : ℝ) ^ l * l.factorial := by positivity
  have key : ∑ i ∈ s, ∑ j ∈ s, c i * c j * eval (x j) (zonal (x i) l) =
      fischer (∑ i ∈ s, C (c i) * zonal (x i) l) (∑ j ∈ s, C (c j) * zonal (x j) l) /
        ((2 : ℝ) ^ l * l.factorial) := by
    rw [fischer_sum_left, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fischer_C_mul_left, fischer_sum_right, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fischer_C_mul_right, fischer_zonal]
    field_simp
  rw [key]
  exact div_nonneg (fischer_self_nonneg _) hk.le

/-! ## Evaluation at unit vectors -/

lemma eval_zonal_unit (x y : Fin 4 → ℝ) (hx : nsq x = 1) (hy : ∑ i, y i ^ 2 = 1) :
    ∀ l : ℕ, eval y (zonal x l) =
      (Polynomial.Chebyshev.U ℝ (l : ℤ)).eval (∑ i, x i * y i)
  | 0 => by simp [zonal]
  | 1 => by simp [zonal, lin, Polynomial.Chebyshev.U_one]
  | (l + 2) => by
    rw [zonal_add_two, map_sub, map_mul, map_mul, map_mul, map_mul, eval_zonal_unit x y hx hy
      (l + 1), eval_zonal_unit x y hx hy l]
    have hcast : ((l + 2 : ℕ) : ℤ) = (l : ℤ) + 2 := by push_cast; ring
    rw [hcast, Polynomial.Chebyshev.U_add_two]
    simp only [eval_C, hx, sq, lin, map_sum, eval_X, map_pow, hy, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, map_mul]
    push_cast
    ring

end Schoenberg

/-- Schoenberg's theorem for `S³` and the Chebyshev polynomials `U_l`, as a proposition. -/
def SchoenbergS3 : Prop :=
  ∀ (l : ℕ) (ι : Type) (s : Finset ι) (x : ι → EuclideanSpace ℝ (Fin 4)) (c : ι → ℝ),
    (∀ i ∈ s, ‖x i‖ = 1) →
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (Polynomial.Chebyshev.U ℝ (l : ℤ)).eval ⟪x i, x j⟫

/-- **Schoenberg (1942) for `S³`**: every `U_l` is positive definite on the unit sphere of `ℝ⁴`. -/
theorem schoenberg_S3 : SchoenbergS3 := by
  intro l ι s x c hx
  have hn : ∀ i ∈ s, Schoenberg.nsq (fun a => (WithLp.ofLp (x i)) a) = 1 := by
    intro i hi
    have h := EuclideanSpace.norm_eq (x i)
    rw [hx i hi] at h
    have h2 : ∑ a, ‖(x i) a‖ ^ 2 = 1 := by
      have h' := congrArg (· ^ 2) h
      simp only [one_pow] at h'
      rw [h', Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simpa [Schoenberg.nsq, Real.norm_eq_abs, sq_abs] using h2
  have key := Schoenberg.zonal_posDef s (fun i a => (WithLp.ofLp (x i)) a) c l
  convert key using 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [Schoenberg.eval_zonal_unit _ _ (hn i hi) (hn j hj) l]
  congr 2
  simp [PiLp.inner_apply, mul_comm]

end D4Bound
