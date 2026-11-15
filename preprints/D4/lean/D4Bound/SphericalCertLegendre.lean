import D4Bound.SchoenbergS2

/-! Normalization and homogeneous form of the S2 Legendre kernel. -/
open Finset MvPolynomial
open scoped RealInnerProductSpace
namespace D4Bound
namespace Schoenberg2

@[simp] lemma legendre_zero (t : ℝ) : legendre 0 t = 1 := by
  simp [legendre, scaledLegendre]
@[simp] lemma legendre_one_degree (t : ℝ) : legendre 1 t = t := by
  simp [legendre, scaledLegendre]

/-- The standard Legendre three-term recurrence; together with degrees zero and one,
this identifies the positive-definite kernel with the normalized Legendre polynomials. -/
lemma legendre_recurrence (l : ℕ) (t : ℝ) :
    legendre (l+2) t = ((2*(l:ℝ)+3)*t*legendre (l+1) t -
      ((l:ℝ)+1)*legendre l t) / ((l:ℝ)+2) := by
  unfold legendre
  rw [scaledLegendre]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (l.factorial : ℝ) ≠ 0 := by positivity
  have h1 : (l:ℝ)+1 ≠ 0 := by positivity
  have h2 : (l:ℝ)+1+1 ≠ 0 := by positivity
  have h3 : (l:ℝ)+2 ≠ 0 := by positivity
  field_simp
  <;> ring

lemma scaledLegendre_at_one : ∀ l, scaledLegendre 1 l = (l.factorial : ℝ)
  | 0 => by simp [scaledLegendre]
  | 1 => by simp [scaledLegendre]
  | l+2 => by
    rw [scaledLegendre,scaledLegendre_at_one (l+1),scaledLegendre_at_one l]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

@[simp] lemma legendre_at_one (l : ℕ) : legendre l 1 = 1 := by
  rw [legendre,scaledLegendre_at_one]
  exact div_self (by positivity)

/-- The polynomial homogeneous Legendre kernel, without square-root singularities. -/
noncomputable def solidLegendre (u v : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => u
  | l+2 => ((2*(l:ℝ)+3)*u*solidLegendre u v (l+1) -
      ((l:ℝ)+1)*v*solidLegendre u v l) / ((l:ℝ)+2)

lemma eval_zonal_general (x y : Fin 3 → ℝ) :
    ∀ l : ℕ, eval y (zonal x l) = (l.factorial : ℝ) *
      solidLegendre (∑ i, x i*y i) (nsq x * nsq y) l
  | 0 => by simp [zonal,solidLegendre]
  | 1 => by simp [zonal,solidLegendre,lin]
  | l+2 => by
    rw [zonal_add_two,map_sub,map_mul,map_mul,map_mul,map_mul,
      eval_zonal_general x y (l+1),eval_zonal_general x y l]
    simp only [eval_C,sq,lin,map_sum,eval_X,map_pow,map_mul,solidLegendre,nsq,
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have h : (l:ℝ)+2 ≠ 0 := by positivity
    field_simp
    <;> ring

/-- Polynomial extension of the Legendre PSD kernel to all vectors, including zero. -/
theorem solidLegendre_posDef {ι : Type*} (s : Finset ι) (x : ι → Fin 3 → ℝ)
    (c : ι → ℝ) (l : ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*
      solidLegendre (∑ a, x i a*x j a) (nsq (x i)*nsq (x j)) l := by
  have hk := zonal_posDef s x c l
  have he : (∑ i ∈ s, ∑ j ∈ s, c i*c j*eval (x j) (zonal (x i) l)) =
      (l.factorial : ℝ) * (∑ i ∈ s, ∑ j ∈ s, c i*c j*
        solidLegendre (∑ a, x i a*x j a) (nsq (x i)*nsq (x j)) l) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [eval_zonal_general]
    ring
  rw [he] at hk
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < (l.factorial:ℝ))).mp hk

end Schoenberg2
#print axioms Schoenberg2.solidLegendre_posDef
end D4Bound
