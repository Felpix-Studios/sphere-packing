import D4Bound.SphericalSurplusSignPairLink0
import D4Bound.SphericalSurplusSignBounds0
import D4Bound.SphericalSurplusCompose
import D4Bound.SphericalConcreteBasic
import D4Bound.SphericalConcreteRepair26
import D4Bound.V7SphericalScalar

/-! Literal surplus instantiation. The theorem ending in `_of_triangle` exposes
exactly the remaining continuous sign statement; it is not asserted here. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.SphericalSurplusBounds.B0
open SphericalSurplusSign SphericalSign SphereCertificate

noncomputable def rawB : ℝ := (130877701570004888847033217319318784541/148723869673221832089000000000000000000)
noncomputable def repairedB : ℝ := (131430224020549714328939307470798784541/148723869673221832089000000000000000000)

theorem scalar_eq (t : ℝ) : g0 t = V7.sphericalScalar t := by rfl

theorem rawB_eq : g0 1 + origin0 = rawB := by
  simpa [rawB,rawBound0] using rawBound0_correct

theorem repairedB_eq : rawB + (24-1)*(epsilon0*SphericalConcrete.C26.D+eta0) = repairedB := by
  norm_num [rawB,repairedB,epsilon0,eta0,SphericalConcrete.C26.D]

theorem repair_psd : SpherePSD SphericalConcrete.C26.T :=
  harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) SphericalConcrete.C26.repairWeights
    (fun i _ => SphericalConcrete.C26.repair_nonneg i)

theorem floor {n : ℕ} (hN : n = 24) (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1) :
    ∀ i, 0 ≤ SphereLocal.energy (anchorKernel kernel0 x) (anchorCoupling coupling0 x) origin0 i := by
  exact physical_anchor_nonneg Finset.univ (rayDegree rays0) (rayO rays0 originDen0)
    (rayV rays0 featureDen0) F0 b0 v0 countM0 x hx (Or.inl (by norm_num [hN,countM0]))

def TriangleSign : Prop := ∀ a b t : ℝ,
  -1 ≤ a → a ≤ 251467/500000 → -1 ≤ b → b ≤ 251467/500000 → -1 ≤ t → t ≤ 251467/500000 →
  0 ≤ 1+2*a*b*t-a^2-b^2-t^2 →
  kernel0 a b t+kernel0 a t b+kernel0 b t a ≤ 3*(epsilon0:ℝ)

theorem raw_upper_of_triangle (hT : TriangleSign) {n : ℕ} (hN : n = 24)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ 251467/500000) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤
      (n:ℝ)*rawB+(eta0:ℝ)*n*(n-1)+(epsilon0:ℝ)*n*(n-1)*(n-2) := by
  have h := raw_spherical_upper g0 coupling0 kernel0 origin0 (251467/500000) epsilon0 eta0
    x hx hxs rawPair0_le hT (floor hN x hx)
  rw [rawB_eq] at h
  simpa only [scalar_eq] using h

theorem repaired_upper_of_triangle (hT : TriangleSign) {n : ℕ} (hN : n = 24)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ 251467/500000) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤ (n:ℝ)*repairedB := by
  have h := repaired_spherical_upper g0 coupling0 SphericalConcrete.C26.T kernel0
    origin0 (251467/500000) epsilon0 eta0 SphericalConcrete.C26.D 24 x hx hxs
    (by norm_num [epsilon0]) (by norm_num [epsilon0,eta0,SphericalConcrete.C26.D])
    (by norm_num [hN]) SphericalConcrete.C26.repair_diag
    (fun t hlo hhi => SphericalConcrete.C26.repair_sign t hlo (by linarith)) repair_psd
    rawPair0_le hT (floor hN x hx)
  rw [rawB_eq,repairedB_eq] at h
  simpa only [scalar_eq] using h

#print axioms raw_upper_of_triangle
#print axioms repaired_upper_of_triangle
end D4Bound.SphericalSurplusBounds.B0
