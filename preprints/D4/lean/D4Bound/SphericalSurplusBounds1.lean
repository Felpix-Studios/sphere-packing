import D4Bound.SphericalSurplusSignPairLink1
import D4Bound.SphericalSurplusSignBounds1
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
namespace D4Bound.SphericalSurplusBounds.B1
open SphericalSurplusSign SphericalSign SphereCertificate

noncomputable def rawB : ℝ := (65914448509406451575062474686557247029/74361934836610916044500000000000000000)
noncomputable def repairedB : ℝ := (7346139720652490896946358445506360781/8262437204067879560500000000000000000)

theorem scalar_eq (t : ℝ) : g1 t = V7.sphericalScalar t := by rfl

theorem rawB_eq : g1 1 + origin1 = rawB := by
  simpa [rawB,rawBound1] using rawBound1_correct

theorem repairedB_eq : rawB + (26-1)*(epsilon1*SphericalConcrete.C26.D+eta1) = repairedB := by
  norm_num [rawB,repairedB,epsilon1,eta1,SphericalConcrete.C26.D]

theorem repair_psd : SpherePSD SphericalConcrete.C26.T :=
  harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) SphericalConcrete.C26.repairWeights
    (fun i _ => SphericalConcrete.C26.repair_nonneg i)

theorem floor {n : ℕ} (hN : n ≤ 26) (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1) :
    ∀ i, 0 ≤ SphereLocal.energy (anchorKernel kernel1 x) (anchorCoupling coupling1 x) origin1 i := by
  exact physical_anchor_nonneg Finset.univ (rayDegree rays1) (rayO rays1 originDen1)
    (rayV rays1 featureDen1) F1 b1 v1 countM1 x hx (Or.inr ⟨by norm_num [b1,bNum1], by norm_num [v1,vNum1], by intro a; simp [F1,correction1,evalZ]⟩)

def TriangleSign : Prop := ∀ a b t : ℝ,
  -1 ≤ a → a ≤ 21/40 → -1 ≤ b → b ≤ 21/40 → -1 ≤ t → t ≤ 21/40 →
  0 ≤ 1+2*a*b*t-a^2-b^2-t^2 →
  kernel1 a b t+kernel1 a t b+kernel1 b t a ≤ 3*(epsilon1:ℝ)

theorem raw_upper_of_triangle (hT : TriangleSign) {n : ℕ} (hN : n ≤ 26)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ 21/40) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤
      (n:ℝ)*rawB+(eta1:ℝ)*n*(n-1)+(epsilon1:ℝ)*n*(n-1)*(n-2) := by
  have h := raw_spherical_upper g1 coupling1 kernel1 origin1 (21/40) epsilon1 eta1
    x hx hxs rawPair1_le hT (floor hN x hx)
  rw [rawB_eq] at h
  simpa only [scalar_eq] using h

theorem repaired_upper_of_triangle (hT : TriangleSign) {n : ℕ} (hN : n ≤ 26)
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ 21/40) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤ (n:ℝ)*repairedB := by
  have h := repaired_spherical_upper g1 coupling1 SphericalConcrete.C26.T kernel1
    origin1 (21/40) epsilon1 eta1 SphericalConcrete.C26.D 26 x hx hxs
    (by norm_num [epsilon1]) (by norm_num [epsilon1,eta1,SphericalConcrete.C26.D])
    (by exact_mod_cast hN) SphericalConcrete.C26.repair_diag
    (fun t hlo hhi => SphericalConcrete.C26.repair_sign t hlo (by linarith)) repair_psd
    rawPair1_le hT (floor hN x hx)
  rw [rawB_eq,repairedB_eq] at h
  simpa only [scalar_eq] using h

#print axioms raw_upper_of_triangle
#print axioms repaired_upper_of_triangle
end D4Bound.SphericalSurplusBounds.B1
