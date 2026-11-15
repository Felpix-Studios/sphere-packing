import D4Bound.SphericalSurplusEnergy
import D4Bound.SphericalCertCompose

/-! Apply scalar pair/triple certificates to finite spherical configurations.
The scalar polynomial can have signed harmonic coefficients: only the anchored
kernel energy, not the scalar energy, needs positivity for this upper bound. -/
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.SphereCertificate

noncomputable def anchorKernel {n : ℕ} (K : ℝ → ℝ → ℝ → ℝ) (x : Fin n → E4)
    (i j k : Fin n) : ℝ := K ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫
noncomputable def anchorCoupling {n : ℕ} (V : ℝ → ℝ) (x : Fin n → E4)
    (i j : Fin n) : ℝ := V ⟪x i,x j⟫

lemma anchor_pair_bound {n : ℕ} (g V : ℝ → ℝ) (K : ℝ → ℝ → ℝ → ℝ)
    (s η : ℝ) (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s)
    (hp : ∀ a, -1 ≤ a → a ≤ s → g a+2*V a+K a a 1 ≤ η) :
    ∀ i j, j ≠ i → g ⟪x i,x j⟫+2*anchorCoupling V x i j+anchorKernel K x i j j ≤ η := by
  intro i j hj
  have hxx : ⟪x j,x j⟫=(1:ℝ) := by rw [real_inner_self_eq_norm_sq,hx]; norm_num
  dsimp [anchorKernel,anchorCoupling]
  rw [hxx]
  exact hp _ (inner_lower_unit _ _ (hx i) (hx j)) (hxs i j hj.symm)

lemma anchor_triangle_bound {n : ℕ} (K : ℝ → ℝ → ℝ → ℝ) (s ε : ℝ)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s)
    (ht : ∀ a b t, -1 ≤ a → a ≤ s → -1 ≤ b → b ≤ s → -1 ≤ t → t ≤ s →
      0 ≤ 1+2*a*b*t-a^2-b^2-t^2 → K a b t+K a t b+K b t a ≤ 3*ε) :
    ∀ i j k, j ≠ i → k ≠ i → k ≠ j →
      SphereLocal.gamma (anchorKernel K x) i j k ≤ 3*ε := by
  intro i j k hj hk hkj
  have h := ht ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫
    (inner_lower_unit _ _ (hx i) (hx j)) (hxs i j hj.symm)
    (inner_lower_unit _ _ (hx i) (hx k)) (hxs i k hk.symm)
    (inner_lower_unit _ _ (hx j) (hx k)) (hxs j k hkj.symm)
    (triple_gram_nonneg _ _ _ (hx i) (hx j) (hx k))
  simpa only [SphereLocal.gamma,anchorKernel,real_inner_comm (x j) (x i),
    real_inner_comm (x k) (x i),real_inner_comm (x k) (x j)] using h

theorem raw_spherical_upper {n : ℕ} (g V : ℝ → ℝ) (K : ℝ → ℝ → ℝ → ℝ)
    (A s ε η : ℝ) (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s)
    (hp : ∀ a, -1 ≤ a → a ≤ s → g a+2*V a+K a a 1 ≤ η)
    (ht : ∀ a b t, -1 ≤ a → a ≤ s → -1 ≤ b → b ≤ s → -1 ≤ t → t ≤ s →
      0 ≤ 1+2*a*b*t-a^2-b^2-t^2 → K a b t+K a t b+K b t a ≤ 3*ε)
    (hf : ∀ i, 0 ≤ SphereLocal.energy (anchorKernel K x) (anchorCoupling V x) A i) :
    (∑ i, ∑ j, g ⟪x i,x j⟫) ≤ (n:ℝ)*(g 1+A)+η*n*(n-1)+ε*n*(n-1)*(n-2) := by
  apply raw_finite_energy_upper (fun i j => g ⟪x i,x j⟫) (anchorKernel K x) (anchorCoupling V x) A (g 1) ε η
  · intro i
    rw [real_inner_self_eq_norm_sq,hx]
    norm_num
  · exact anchor_pair_bound g V K s η x hx hxs hp
  · exact anchor_triangle_bound K s ε x hx hxs ht
  · exact hf

theorem repaired_spherical_upper {n : ℕ} (g V T : ℝ → ℝ) (K : ℝ → ℝ → ℝ → ℝ)
    (A s ε η D M : ℝ) (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s)
    (hε : 0 ≤ ε) (hδ : 0 ≤ ε*D+η) (hM : (n:ℝ) ≤ M)
    (hTdiag : T 1=D) (hTsign : ∀ t, -1 ≤ t → t ≤ s → T t ≤ -1)
    (hTpsd : SpherePSD T)
    (hp : ∀ a, -1 ≤ a → a ≤ s → g a+2*V a+K a a 1 ≤ η)
    (ht : ∀ a b t, -1 ≤ a → a ≤ s → -1 ≤ b → b ≤ s → -1 ≤ t → t ≤ s →
      0 ≤ 1+2*a*b*t-a^2-b^2-t^2 → K a b t+K a t b+K b t a ≤ 3*ε)
    (hf : ∀ i, 0 ≤ SphereLocal.energy (anchorKernel K x) (anchorCoupling V x) A i) :
    (∑ i, ∑ j, g ⟪x i,x j⟫) ≤ (n:ℝ)*(g 1+A+(M-1)*(ε*D+η)) := by
  apply psd_repaired_energy_upper (fun i j => g ⟪x i,x j⟫) (anchorKernel K x) (anchorCoupling V x) (fun i j => T ⟪x i,x j⟫) A (g 1) ε η D M hε hδ hM
  · intro i; rw [real_inner_self_eq_norm_sq,hx]; norm_num
  · intro i; rw [real_inner_self_eq_norm_sq,hx]; simpa using hTdiag
  · exact anchor_pair_bound g V K s η x hx hxs hp
  · exact anchor_triangle_bound K s ε x hx hxs ht
  · intro i j hij
    exact hTsign _ (inner_lower_unit _ _ (hx i) (hx j)) (hxs i j hij)
  · exact hf
  · intro i
    have hp := hTpsd n x hx (fun j => if j ≠ i then 1 else 0)
    convert hp using 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

theorem physical_anchor_nonneg {n : ℕ} {ρ : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (o : ρ → ℝ) (v : ρ → ℝ → ℝ) (F : ℝ → ℝ) (b v0 m : ℝ)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hcount : (n:ℝ)-1=m ∨ (b=0 ∧ v0=0 ∧ ∀ a, F a=0)) :
    ∀ i, 0 ≤ SphereLocal.energy
      (anchorKernel (fun a c t => kernel R l v a c t+b+F a+F c) x)
      (anchorCoupling (fun a => coupling R l o v a+v0-m*F a) x)
      (origin R l o-2*m*v0-m^2*b) i := by
  intro i
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i)
  have hS : (S.card:ℝ)=(n:ℝ)-1 := by
    have h := sum_nonanchor_one i
    simpa only [Finset.sum_boole] using h
  have hnonneg : 0 ≤ (origin R l o-2*m*v0-m^2*b) +
      2*∑ j ∈ S, (coupling R l o v ⟪x i,x j⟫+v0-m*F ⟪x i,x j⟫) +
      (∑ j ∈ S, ∑ k ∈ S, (kernel R l v ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫+b+F ⟪x i,x j⟫+F ⟪x i,x k⟫)) := by
    rcases hcount with hm | ⟨hb,hv,hF⟩
    · exact fixed_count_energy_nonneg R l o v S (x i) (hx i) x (fun j _ => hx j)
        F b v0 m (hS.trans hm)
    · simp only [hb,hv,hF,mul_zero,sub_zero,add_zero]
      exact energy_nonneg R l o v S (x i) (hx i) x (fun j _ => hx j)
  have hdouble : (∑ j ∈ S, ∑ k ∈ S,
      (kernel R l v ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫+b+F ⟪x i,x j⟫+F ⟪x i,x k⟫)) =
      ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then
        (kernel R l v ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫+b+F ⟪x i,x j⟫+F ⟪x i,x k⟫) else 0 := by
    simp only [S,Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ≠ i
    · simp only [if_pos hj]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hj]
    · simp [hj]
  rw [hdouble] at hnonneg
  simpa only [SphereLocal.energy,anchorKernel,anchorCoupling,S,Finset.sum_filter] using hnonneg

end D4Bound.SphereCertificate
#print axioms D4Bound.SphereCertificate.raw_spherical_upper
#print axioms D4Bound.SphereCertificate.repaired_spherical_upper
#print axioms D4Bound.SphereCertificate.physical_anchor_nonneg
