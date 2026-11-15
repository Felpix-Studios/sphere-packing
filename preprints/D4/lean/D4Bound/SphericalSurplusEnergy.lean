import D4Bound.SphericalCertRepair

/-! Fixed-cardinality Gram restrictions and exact finite-count surplus bounds.
These identities retain the common scalar polynomial unchanged. -/
set_option maxHeartbeats 0
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.SphereCertificate

/-- Restoring a free constant radial feature changes the anchored energy by a
multiple of the difference between the actual and prescribed neighbour counts. -/
theorem fixed_count_energy_identity {ι : Type*} (s : Finset ι)
    (K : ι → ι → ℝ) (V F : ι → ℝ) (A b v m : ℝ) :
    (A-2*m*v-m^2*b) + 2*∑ i ∈ s, (V i+v-m*F i) +
      (∑ i ∈ s, ∑ j ∈ s, (K i j+b+F i+F j)) =
      (A+2*∑ i ∈ s, V i+(∑ i ∈ s, ∑ j ∈ s, K i j)) +
        2*((s.card:ℝ)-m)*v + ((s.card:ℝ)^2-m^2)*b +
          2*((s.card:ℝ)-m)*(∑ i ∈ s, F i) := by
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    nsmul_eq_mul]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem fixed_count_energy_nonneg {ρ ι : Type*} (R : Finset ρ) (l : ρ → ℕ)
    (o : ρ → ℝ) (v : ρ → ℝ → ℝ) (s : Finset ι) (w : E4) (hw : ‖w‖=1)
    (x : ι → E4) (hx : ∀ i ∈ s, ‖x i‖=1) (F : ℝ → ℝ) (b v0 m : ℝ)
    (hcard : (s.card:ℝ)=m) :
    0 ≤ (origin R l o-2*m*v0-m^2*b) +
      2*∑ i ∈ s, (coupling R l o v ⟪w,x i⟫+v0-m*F ⟪w,x i⟫) +
      (∑ i ∈ s, ∑ j ∈ s,
        (kernel R l v ⟪w,x i⟫ ⟪w,x j⟫ ⟪x i,x j⟫+b+F ⟪w,x i⟫+F ⟪w,x j⟫)) := by
  rw [fixed_count_energy_identity,hcard]
  simpa using energy_nonneg R l o v s w hw x hx

lemma sum_nonanchor_one {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j ≠ i then (1:ℝ) else 0) = (n:ℝ)-1 := by
  have h : ∀ j : Fin n, (if j ≠ i then (1:ℝ) else 0) = 1-(if j=i then 1 else 0) := by
    intro j
    by_cases hj : j=i <;> simp [hj]
  simp only [h,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma sum_nonanchor_const {n : ℕ} (i : Fin n) (a : ℝ) :
    (∑ j : Fin n, if j ≠ i then a else 0) = ((n:ℝ)-1)*a := by
  have h : ∀ j : Fin n, (if j ≠ i then a else 0) = (if j ≠ i then 1 else 0)*a := by
    intro j
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => h j, ← Finset.sum_mul,sum_nonanchor_one]

lemma sum_nonanchor_double_const {n : ℕ} (i : Fin n) (a : ℝ) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ i ∧ k ≠ i then a else 0) = ((n:ℝ)-1)^2*a := by
  have h : ∀ j : Fin n,
      (∑ k : Fin n, if j ≠ i ∧ k ≠ i then a else 0) =
        (if j ≠ i then ((n:ℝ)-1)*a else 0) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · simpa [hj] using sum_nonanchor_const i a
  rw [Finset.sum_congr rfl fun j _ => h j,sum_nonanchor_const]
  ring

/-- Keep the common scalar unchanged and charge the pair and cyclic tolerances
using their exact finite multiplicities. This is the sharper finite-count credit. -/
theorem raw_finite_energy_upper {n : ℕ} (g : Fin n → Fin n → ℝ)
    (K : Fin n → Fin n → Fin n → ℝ) (v : Fin n → Fin n → ℝ) (A B ε η : ℝ)
    (hdiag : ∀ i, g i i=B)
    (hpair : ∀ i j, j ≠ i → g i j+2*v i j+K i j j ≤ η)
    (hgamma : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K i j k ≤ 3*ε)
    (hfloor : ∀ i, 0 ≤ SphereLocal.energy K v A i) :
    (∑ i, ∑ j, g i j) ≤ (n:ℝ)*(B+A) + η*n*(n-1) + ε*n*(n-1)*(n-2) := by
  let K' : Fin n → Fin n → Fin n → ℝ := fun i j k => K i j k-ε
  let v' : Fin n → Fin n → ℝ := fun i j => v i j+(ε-η)/2
  let β : ℝ := -η*((n:ℝ)-1)-ε*((n:ℝ)-1)*((n:ℝ)-2)
  have hp : ∀ i j, j ≠ i → g i j+2*v' i j+K' i j j ≤ 0 := by
    intro i j hj
    dsimp [v',K']
    linarith [hpair i j hj]
  have ht : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K' i j k ≤ 0 := by
    intro i j k hj hk hkj
    have h := hgamma i j k hj hk hkj
    dsimp [SphereLocal.gamma,K'] at *
    linarith
  have hf : ∀ i, β ≤ SphereLocal.energy K' v' A i := by
    intro i
    have hv : (∑ j, if j ≠ i then v' i j else 0) =
        (∑ j, if j ≠ i then v i j else 0) + ((n:ℝ)-1)*((ε-η)/2) := by
      rw [← sum_nonanchor_const i ((ε-η)/2),← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [v']; split_ifs <;> ring
    have hk : (∑ j, ∑ k, if j ≠ i ∧ k ≠ i then K' i j k else 0) =
        (∑ j, ∑ k, if j ≠ i ∧ k ≠ i then K i j k else 0) - ((n:ℝ)-1)^2*ε := by
      rw [← sum_nonanchor_double_const i ε]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      dsimp [K']; split_ifs <;> ring
    have hh := hfloor i
    unfold SphereLocal.energy at *
    rw [hv,hk]
    dsimp [β]
    nlinarith
  have h := SphereLocal.finite_local_energy g K' v' A β B hdiag hp ht hf
  convert h using 1 <;> dsimp [β] <;> ring

/-- PSD uniform repair gives the second (constant-per-point) surplus bound,
again with the common scalar unchanged. -/
theorem psd_repaired_energy_upper {n : ℕ} (g : Fin n → Fin n → ℝ)
    (K : Fin n → Fin n → Fin n → ℝ) (v : Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ) (A B ε η D M : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ ε*D+η) (hM : (n:ℝ) ≤ M)
    (hdiag : ∀ i, g i i=B) (hTdiag : ∀ i, T i i=D)
    (hpair : ∀ i j, j ≠ i → g i j+2*v i j+K i j j ≤ η)
    (hgamma : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K i j k ≤ 3*ε)
    (hTsign : ∀ i j, i ≠ j → T i j ≤ -1)
    (hfloor : ∀ i, 0 ≤ SphereLocal.energy K v A i)
    (hTpsd : ∀ i, 0 ≤ ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then T j k else 0) :
    (∑ i, ∑ j, g i j) ≤ (n:ℝ)*(B+A+(M-1)*(ε*D+η)) := by
  have h := repaired_energy_upper g K v T A B ε η D hε hdiag hTdiag
    hpair hgamma hTsign hfloor hTpsd
  have hh := mul_nonneg (sub_nonneg.mpr hM) hδ
  have hhh := mul_nonneg (show (0:ℝ) ≤ n by positivity) hh
  nlinarith

end D4Bound.SphereCertificate
#print axioms D4Bound.SphereCertificate.fixed_count_energy_nonneg
#print axioms D4Bound.SphereCertificate.raw_finite_energy_upper
#print axioms D4Bound.SphereCertificate.psd_repaired_energy_upper
