import D4Bound.SphericalCertEnergy

/-! Exact uniform repair and code-bound composition. These lemmas account for
both the scalar constant decrease and the positive semidefinite kernel repair. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
namespace SphereCertificate

/-- Positive harmonic sums with nonnegative coefficients are PSD on every
finite indexed family, with arbitrary real weights. -/
theorem harmonic_energy_nonneg {ι : Type} {ρ : Type*} (s : Finset ι) (R : Finset ρ)
    (degree : ρ → ℕ) (a : ρ → ℝ) (ha : ∀ r ∈ R, 0 ≤ a r)
    (x : ι → E4) (hx : ∀ i ∈ s, ‖x i‖=1) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*
      (∑ r ∈ R, a r*(Polynomial.Chebyshev.U ℝ (degree r : ℤ)).eval ⟪x i,x j⟫) := by
  have he : (∑ i ∈ s, ∑ j ∈ s, c i*c j*
      (∑ r ∈ R, a r*(Polynomial.Chebyshev.U ℝ (degree r : ℤ)).eval ⟪x i,x j⟫)) =
      ∑ r ∈ R, a r*(∑ i ∈ s, ∑ j ∈ s,
        c i*c j*(Polynomial.Chebyshev.U ℝ (degree r : ℤ)).eval ⟪x i,x j⟫) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [he]
  exact Finset.sum_nonneg fun r hr => mul_nonneg (ha r hr)
    (schoenberg_S3 (degree r) ι s x c hx)

/-- PSD repair restricted to the nonanchor indices. -/
theorem harmonic_nonanchor_nonneg {n : ℕ} {ρ : Type*} (R : Finset ρ)
    (degree : ρ → ℕ) (a : ρ → ℝ) (ha : ∀ r ∈ R, 0 ≤ a r)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1) (anchor : Fin n) :
    0 ≤ ∑ j, ∑ k, (if j ≠ anchor ∧ k ≠ anchor then
      (∑ r ∈ R, a r*(Polynomial.Chebyshev.U ℝ (degree r : ℤ)).eval ⟪x j,x k⟫) else 0) := by
  have hp := harmonic_energy_nonneg Finset.univ R degree a ha x (fun i _ => hx i)
    (fun i => if i ≠ anchor then 1 else 0)
  convert hp using 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hj : j=anchor <;> by_cases hk : k=anchor <;> simp [hj,hk]

/-- Uniform repair turns the checked raw pair and triangle tolerances into exact
signs. The energy floor is preserved by an independently proved PSD repair. -/
theorem repaired_energy_upper {n : ℕ} (g : Fin n → Fin n → ℝ)
    (K : Fin n → Fin n → Fin n → ℝ) (v : Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ) (A B ε η D : ℝ)
    (hε : 0 ≤ ε) (hdiag : ∀ i, g i i = B) (hTdiag : ∀ i, T i i = D)
    (hpair : ∀ i j, j ≠ i → g i j + 2*v i j + K i j j ≤ η)
    (hgamma : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K i j k ≤ 3*ε)
    (hTsign : ∀ i j, i ≠ j → T i j ≤ -1)
    (hfloor : ∀ i, 0 ≤ SphereLocal.energy K v A i)
    (hTpsd : ∀ i, 0 ≤ ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then T j k else 0) :
    (∑ i, ∑ j, g i j) - (n:ℝ)^2*(ε*D+η) ≤
      n*(B-(ε*D+η)+A) := by
  let g' : Fin n → Fin n → ℝ := fun i j => g i j-(ε*D+η)
  let K' : Fin n → Fin n → Fin n → ℝ := fun i j k => K i j k+ε*T j k
  have hp : ∀ i j, j ≠ i → g' i j+2*v i j+K' i j j ≤ 0 := by
    intro i j hj
    dsimp [g',K']
    rw [hTdiag]
    linarith [hpair i j hj]
  have ht : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K' i j k ≤ 0 := by
    intro i j k hj hk hkj
    have h1 := mul_le_mul_of_nonneg_left (hTsign j k hkj.symm) hε
    have h2 := mul_le_mul_of_nonneg_left (hTsign i k hk.symm) hε
    have h3 := mul_le_mul_of_nonneg_left (hTsign i j hj.symm) hε
    have hraw := hgamma i j k hj hk hkj
    dsimp [SphereLocal.gamma,K'] at *
    linarith
  have hf : ∀ i, 0 ≤ SphereLocal.energy K' v A i := by
    intro i
    have hs : (∑ j, ∑ k, (if j ≠ i ∧ k ≠ i then K' i j k else 0)) =
        (∑ j, ∑ k, (if j ≠ i ∧ k ≠ i then K i j k else 0)) +
          ε*(∑ j, ∑ k, if j ≠ i ∧ k ≠ i then T j k else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      dsimp [K']
      split_ifs <;> ring
    unfold SphereLocal.energy
    rw [hs]
    have hraw := hfloor i
    unfold SphereLocal.energy at hraw
    linarith [mul_nonneg hε (hTpsd i)]
  have hb := SphereLocal.finite_local_energy g' K' v A 0 (B-(ε*D+η))
    (by intro i; dsimp [g']; rw [hdiag]) hp ht hf
  simp only [g',Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,sub_zero] at hb
  convert hb using 1 <;> ring

/-- A repaired spherical certificate proves the integer count at its exact
objective. No rounded objective is used. -/
theorem repaired_code_count {n : ℕ} (m : ℕ) (g : Fin n → Fin n → ℝ)
    (K : Fin n → Fin n → Fin n → ℝ) (v : Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ) (A B ε η D : ℝ)
    (hε : 0 ≤ ε) (hdiag : ∀ i, g i i = B) (hTdiag : ∀ i, T i i = D)
    (hpair : ∀ i j, j ≠ i → g i j + 2*v i j + K i j j ≤ η)
    (hgamma : ∀ i j k, j ≠ i → k ≠ i → k ≠ j → SphereLocal.gamma K i j k ≤ 3*ε)
    (hTsign : ∀ i j, i ≠ j → T i j ≤ -1)
    (hfloor : ∀ i, 0 ≤ SphereLocal.energy K v A i)
    (hTpsd : ∀ i, 0 ≤ ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then T j k else 0)
    (hscalar : (n:ℝ)^2 ≤ ∑ i, ∑ j, g i j)
    (hdecrease : ε*D+η < 1)
    (hobjective : B+A-(ε*D+η) < (m+1:ℕ)*(1-(ε*D+η))) : n ≤ m := by
  have hbound := repaired_energy_upper g K v T A B ε η D hε hdiag hTdiag
    hpair hgamma hTsign hfloor hTpsd
  by_contra h
  have hnm : (m+1:ℕ) ≤ n := by omega
  have hn : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnr : ((m+1:ℕ):ℝ) ≤ n := by exact_mod_cast hnm
  have hpos : 0 < 1-(ε*D+η) := by linarith
  have hh := mul_le_mul_of_nonneg_right hnr hpos.le
  have hh' : B+A-(ε*D+η) < (n:ℝ)*(1-(ε*D+η)) := lt_of_lt_of_le hobjective hh
  have hm := mul_lt_mul_of_pos_left hh' hn
  nlinarith

end SphereCertificate
#print axioms SphereCertificate.repaired_code_count
end D4Bound
