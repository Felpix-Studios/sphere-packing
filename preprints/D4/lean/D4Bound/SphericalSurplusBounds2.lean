import D4Bound.SphericalSurplusSignPairLink2
import D4Bound.SphericalSurplusSignBounds2
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
namespace D4Bound.SphericalSurplusBounds.B2
open SphericalSurplusSign SphericalSign SphereCertificate

noncomputable def rawB : ℝ := (32684678624403525301964627843417351227/37180967418305458022250000000000000000)
noncomputable def repairedB : ℝ := (32781066933107189220742908478457351227/37180967418305458022250000000000000000)

theorem scalar_eq (t : ℝ) : g2 t = V7.sphericalScalar t := by rfl

theorem rawB_eq : g2 1 + origin2 = rawB := by
  simpa [rawB,rawBound2] using rawBound2_correct

theorem repairedB_eq : rawB + (25-1)*(epsilon2*SphericalConcrete.C26.D+eta2) = repairedB := by
  norm_num [rawB,repairedB,epsilon2,eta2,SphericalConcrete.C26.D]

theorem repair_psd : SpherePSD SphericalConcrete.C26.T :=
  harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) SphericalConcrete.C26.repairWeights
    (fun i _ => SphericalConcrete.C26.repair_nonneg i)

theorem floor {n : ℕ} (hN : n = 25) (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1) :
    ∀ i, 0 ≤ SphereLocal.energy (anchorKernel kernel2 x) (anchorCoupling coupling2 x) origin2 i := by
  exact physical_anchor_nonneg Finset.univ (rayDegree rays2) (rayO rays2 originDen2)
    (rayV rays2 featureDen2) F2 b2 v2 countM2 x hx (Or.inl (by norm_num [hN,countM2]))

def TriangleSign : Prop := ∀ a b t : ℝ,
  -1 ≤ a → a ≤ 103/200 → -1 ≤ b → b ≤ 103/200 → -1 ≤ t → t ≤ 103/200 →
  0 ≤ 1+2*a*b*t-a^2-b^2-t^2 →
  kernel2 a b t+kernel2 a t b+kernel2 b t a ≤ 3*(epsilon2:ℝ)

theorem raw_upper_of_triangle (hT : TriangleSign) {n : ℕ} (hN : n = 25)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ 103/200) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤
      (n:ℝ)*rawB+(eta2:ℝ)*n*(n-1)+(epsilon2:ℝ)*n*(n-1)*(n-2) := by
  have h := raw_spherical_upper g2 coupling2 kernel2 origin2 (103/200) epsilon2 eta2
    x hx hxs rawPair2_le hT (floor hN x hx)
  rw [rawB_eq] at h
  simpa only [scalar_eq] using h

theorem repaired_upper_of_triangle (hT : TriangleSign) {n : ℕ} (hN : n = 25)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ 103/200) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤ (n:ℝ)*repairedB := by
  have h := repaired_spherical_upper g2 coupling2 SphericalConcrete.C26.T kernel2
    origin2 (103/200) epsilon2 eta2 SphericalConcrete.C26.D 25 x hx hxs
    (by norm_num [epsilon2]) (by norm_num [epsilon2,eta2,SphericalConcrete.C26.D])
    (by norm_num [hN]) SphericalConcrete.C26.repair_diag
    (fun t hlo hhi => SphericalConcrete.C26.repair_sign t hlo (by linarith)) repair_psd
    rawPair2_le hT (floor hN x hx)
  rw [rawB_eq,repairedB_eq] at h
  simpa only [scalar_eq] using h

#print axioms raw_upper_of_triangle
#print axioms repaired_upper_of_triangle
end D4Bound.SphericalSurplusBounds.B2
