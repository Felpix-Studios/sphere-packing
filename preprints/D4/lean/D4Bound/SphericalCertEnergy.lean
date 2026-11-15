import D4Bound.SphericalCertTransverse
import D4Bound.SphericalCertLocal
import D4Bound.SphericalCertBasic

/-! Positivity and repair of the spherical anchored energies.
The radial features are arbitrary: they will be instantiated with the exact
rational Chebyshev features and integer Gram rays from the certificates. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
namespace SphereCertificate

noncomputable def rayKernel (l : ℕ) (v : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  v a * v b * Schoenberg2.solidLegendre (t-a*b) ((1-a^2)*(1-b^2)) l

noncomputable def rayOrigin (l : ℕ) (o : ℝ) : ℝ := if l = 0 then o else 0

noncomputable def kernel {ρ : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (v : ρ → ℝ → ℝ) (a b t : ℝ) : ℝ := ∑ r ∈ R, rayKernel (l r) (v r) a b t

noncomputable def origin {ρ : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (o : ρ → ℝ) : ℝ := ∑ r ∈ R, rayOrigin (l r) (o r)^2

noncomputable def coupling {ρ : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (o : ρ → ℝ) (v : ρ → ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑ r ∈ R, rayOrigin (l r) (o r) * v r a

/-- Degree zero is a square, and each other degree is a positive Legendre kernel
on the anchor's orthogonal complement. -/
theorem ray_energy_nonneg {ι : Type*} (s : Finset ι) (w : E4) (hw : ‖w‖=1)
    (x : ι → E4) (hx : ∀ i ∈ s, ‖x i‖=1) (v : ℝ → ℝ) (l : ℕ) (o : ℝ) :
    0 ≤ rayOrigin l o ^ 2 + 2 * ∑ i ∈ s, rayOrigin l o * v ⟪w,x i⟫ +
      ∑ i ∈ s, ∑ j ∈ s, rayKernel l v ⟪w,x i⟫ ⟪w,x j⟫ ⟪x i,x j⟫ := by
  by_cases hl : l=0
  · subst l
    simp only [rayOrigin,rayKernel,Schoenberg2.solidLegendre,mul_one,ite_true]
    rw [← Finset.mul_sum, ← Finset.sum_mul_sum]
    nlinarith [sq_nonneg (o + ∑ i ∈ s, v ⟪w,x i⟫)]
  · simp only [rayOrigin,if_neg hl,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,
      Finset.sum_const_zero,mul_zero,zero_add]
    exact anchored_legendre_posDef s w hw x hx (fun i => v ⟪w,x i⟫) l

/-- Sum-of-rays positivity includes the origin row and all cross terms. -/
theorem energy_nonneg {ρ ι : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (o : ρ → ℝ) (v : ρ → ℝ → ℝ) (s : Finset ι) (w : E4) (hw : ‖w‖=1)
    (x : ι → E4) (hx : ∀ i ∈ s, ‖x i‖=1) :
    0 ≤ origin R l o + 2 * ∑ i ∈ s, coupling R l o v ⟪w,x i⟫ +
      ∑ i ∈ s, ∑ j ∈ s, kernel R l v ⟪w,x i⟫ ⟪w,x j⟫ ⟪x i,x j⟫ := by
  have hp := Finset.sum_nonneg (fun r (hr : r ∈ R) => ray_energy_nonneg s w hw x hx (v r) (l r) (o r))
  have hc : (∑ i ∈ s, coupling R l o v ⟪w,x i⟫) =
      ∑ r ∈ R, ∑ i ∈ s, rayOrigin (l r) (o r) * v r ⟪w,x i⟫ := by
    unfold coupling
    exact Finset.sum_comm
  have hk : (∑ i ∈ s, ∑ j ∈ s, kernel R l v ⟪w,x i⟫ ⟪w,x j⟫ ⟪x i,x j⟫) =
      ∑ r ∈ R, ∑ i ∈ s, ∑ j ∈ s, rayKernel (l r) (v r) ⟪w,x i⟫ ⟪w,x j⟫ ⟪x i,x j⟫ := by
    unfold kernel
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  rw [hc,hk]
  simpa only [origin,Finset.sum_add_distrib,Finset.mul_sum] using hp

end SphereCertificate

#print axioms SphereCertificate.energy_nonneg
end D4Bound
