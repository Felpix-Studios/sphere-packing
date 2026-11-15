import D4Bound.SphericalCertRepair
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Geometry and final composition interface for the three spherical count
certificates. Literal certificate signs are proved separately. -/
open Finset
open scoped RealInnerProductSpace
set_option maxHeartbeats 300000
set_option Elab.async false
namespace D4Bound
namespace SphereCertificate

def SpherePSD (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → E4), (∀ i, ‖x i‖=1) → ∀ c : Fin n → ℝ,
    0 ≤ ∑ i, ∑ j, c i*c j*f ⟪x i,x j⟫

theorem harmonic_PSD {ρ : Type*} (R : Finset ρ) (degree : ρ → ℕ)
    (a : ρ → ℝ) (ha : ∀ r ∈ R, 0 ≤ a r) :
    SpherePSD (fun t => ∑ r ∈ R, a r*(Polynomial.Chebyshev.U ℝ (degree r : ℤ)).eval t) := by
  intro n x hx c
  exact harmonic_energy_nonneg Finset.univ R degree a ha x (fun i _ => hx i) c

#print axioms harmonic_PSD

lemma triple_gram_nonneg (x y z : E4) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) :
    0 ≤ 1+2*⟪x,y⟫*⟪x,z⟫*⟪y,z⟫-⟪x,y⟫^2-⟪x,z⟫^2-⟪y,z⟫^2 := by
  have hp := (Matrix.posSemidef_gram ℝ ![x,y,z]).det_nonneg
  rw [Matrix.det_fin_three] at hp
  simp only [Matrix.gram,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,real_inner_self_eq_norm_sq,hx,hy,hz,one_pow] at hp
  simp only [real_inner_comm x y,real_inner_comm x z,real_inner_comm y z] at hp
  nlinarith only [hp]

#print axioms triple_gram_nonneg

lemma inner_lower_unit (x y : E4) (hx : ‖x‖=1) (hy : ‖y‖=1) : -1 ≤ ⟪x,y⟫ := by
  have hp := (abs_le.mp (abs_real_inner_le_norm x y)).1
  simpa [hx,hy] using hp

/-- Composition in the exact source interface. `kernel`, `coupling`, and `origin`
are the same sum-of-rays expressions used for positivity and for the checked
polynomial expansions. -/
theorem code_bound_from_rays {ρ : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (o : ρ → ℝ) (v : ρ → ℝ → ℝ) (g T : ℝ → ℝ) (s ε η D : ℝ) (m : ℕ)
    (hscalar : SpherePSD (fun t => g t-1)) (hrepair : SpherePSD T)
    (hε : 0 ≤ ε) (hTdiag : T 1 = D)
    (hTsign : ∀ t, -1 ≤ t → t ≤ s → T t ≤ -1)
    (hpair : ∀ a, -1 ≤ a → a ≤ s →
      g a + 2*coupling R l o v a + kernel R l v a a 1 ≤ η)
    (htriangle : ∀ a b t, -1 ≤ a → a ≤ s → -1 ≤ b → b ≤ s → -1 ≤ t → t ≤ s →
      0 ≤ 1+2*a*b*t-a^2-b^2-t^2 →
      kernel R l v a b t + kernel R l v a t b + kernel R l v b t a ≤ 3*ε)
    (hdecrease : ε*D+η < 1)
    (hobjective : g 1 + origin R l o - (ε*D+η) < (m+1:ℕ)*(1-(ε*D+η))) :
    SphericalCodeBound s m := by
  classical
  intro C hC hsep
  let e : Fin C.card ≃ C := C.equivFin.symm
  let x : Fin C.card → E4 := fun i => (e i).val
  have hx : ∀ i, ‖x i‖=1 := fun i => hC _ (e i).property
  have hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ s := by
    intro i j hij
    apply hsep _ (e i).property _ (e j).property
    intro h
    apply hij
    exact e.injective (Subtype.ext h)
  let G : Fin C.card → Fin C.card → ℝ := fun i j => g ⟪x i,x j⟫
  let K : Fin C.card → Fin C.card → Fin C.card → ℝ := fun i j k =>
    kernel R l v ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫
  let V : Fin C.card → Fin C.card → ℝ := fun i j => coupling R l o v ⟪x i,x j⟫
  let TT : Fin C.card → Fin C.card → ℝ := fun i j => T ⟪x i,x j⟫
  have hxx : ∀ i, ⟪x i,x i⟫=(1:ℝ) := by
    intro i
    rw [real_inner_self_eq_norm_sq,hx]
    norm_num
  have hGdiag : ∀ i, G i i=g 1 := by intro i; dsimp [G]; rw [hxx]
  have hTTdiag : ∀ i, TT i i=D := by intro i; dsimp [TT]; rw [hxx,hTdiag]
  have hP : ∀ i j, j ≠ i → G i j+2*V i j+K i j j ≤ η := by
    intro i j hj
    dsimp [G,V,K]
    rw [hxx]
    exact hpair _ (inner_lower_unit _ _ (hx i) (hx j)) (hxs i j hj.symm)
  have hT : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K i j k ≤ 3*ε := by
    intro i j k hj hk hkj
    have ht := htriangle ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫
      (inner_lower_unit _ _ (hx i) (hx j)) (hxs i j hj.symm)
      (inner_lower_unit _ _ (hx i) (hx k)) (hxs i k hk.symm)
      (inner_lower_unit _ _ (hx j) (hx k)) (hxs j k hkj.symm)
      (triple_gram_nonneg _ _ _ (hx i) (hx j) (hx k))
    simpa only [SphereLocal.gamma,K,real_inner_comm (x j) (x i),
      real_inner_comm (x k) (x i),real_inner_comm (x k) (x j)] using ht
  have hTS : ∀ i j, i ≠ j → TT i j ≤ -1 := by
    intro i j hij
    exact hTsign _ (inner_lower_unit _ _ (hx i) (hx j)) (hxs i j hij)
  have hF : ∀ i, 0 ≤ SphereLocal.energy K V (origin R l o) i := by
    intro i
    let S : Finset (Fin C.card) := Finset.univ.filter (fun j => j ≠ i)
    have hp := energy_nonneg R l o v S (x i) (hx i) x (fun j _ => hx j)
    have hdouble : (∑ j ∈ S, ∑ k ∈ S, kernel R l v ⟪x i,x j⟫ ⟪x i,x k⟫ ⟪x j,x k⟫) =
        ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then K i j k else 0 := by
      simp only [S,Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ≠ i
      · simp only [if_pos hj]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hj,K]
      · simp [hj]
    rw [hdouble] at hp
    simpa only [SphereLocal.energy,V,S,Finset.sum_filter] using hp
  have hTP : ∀ i, 0 ≤ ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then TT j k else 0 := by
    intro i
    have hp := hrepair C.card x hx (fun j => if j ≠ i then 1 else 0)
    convert hp using 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk,TT]
  have hS : (C.card:ℝ)^2 ≤ ∑ i, ∑ j, G i j := by
    have hp := hscalar C.card x hx (fun _ => 1)
    simp only [mul_one,one_mul,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hp
    dsimp [G]
    nlinarith
  exact repaired_code_count m G K V TT (origin R l o) (g 1) ε η D
    hε hGdiag hTTdiag hP hT hTS hF hTP hS hdecrease hobjective

end SphereCertificate
#print axioms SphereCertificate.code_bound_from_rays
end D4Bound
