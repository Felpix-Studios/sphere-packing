import D4Bound.V7Kernel
import D4Bound.ComponentsGauge

/-!
# Concrete V7 energy decomposition

The component identities here concern the actual `V7.kernel` definition. They
do not assume the census floor. The separate lower bounds for the Gram,
spherical and discarded components must still be proved before this becomes
a proof of `CensusFloor V7.kernel`.
-/

open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

def radialEnergy (A : ℝ) (h : ℝ → ℝ) (k : ℝ → ℝ → ℝ → ℝ) (X : Finset E4) : ℝ :=
  A + 2 * ∑ x ∈ X, h ‖x‖ +
    ∑ x ∈ X, ∑ y ∈ X, k ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖))

def capsLinear (r : ℝ) : ℝ :=
  (caps.map fun c => (c.weight : ℝ)*(c.multiplicity : ℝ)*capWeight c r/2).sum

def tentsLinear (r : ℝ) : ℝ :=
  (tents.map fun c => (c.weight : ℝ)*(c.capacity : ℝ)*radialValue c.vector r/2).sum

def allocationsLinear (r : ℝ) : ℝ :=
  (allocations.map fun c => (c.weight : ℝ)*radialValue c.vector r/2).sum

def sphericalLinear (r : ℝ) : ℝ :=
  (sphericalRays.map fun c => (c.weight : ℝ)*(c.bound : ℝ)*indicator c.radius r/2).sum

def conditionalLinear (r : ℝ) : ℝ :=
  (conditionalRays.map fun c => 23*(c.weight : ℝ)*
    (indicator c.outer r-indicator c.inner r)/2).sum

def countsLinear (r : ℝ) : ℝ := (countPolynomials.map fun c => countLinear c r).sum
def countsPair (r s : ℝ) : ℝ := (countPolynomials.map fun c => countPair c r s).sum
def countOriginQ : ℚ := (countPolynomials.map fun c => c.weight*c.constant).sum
def graphOriginQ : ℚ := (graphs.map fun g => g.weight*g.capacity).sum

def gramEnergy (X : Finset E4) : ℝ :=
  radialEnergy gramOrigin (radialValue originVector) gramPair X
def capsEnergy (X : Finset E4) : ℝ :=
  radialEnergy 0 capsLinear (fun r s t => -capsCorrection r s t) X
def tentsEnergy (X : Finset E4) : ℝ :=
  radialEnergy 0 tentsLinear (fun r s t => -tentsCorrection r s t) X
def allocationsEnergy (X : Finset E4) : ℝ :=
  radialEnergy 0 allocationsLinear (fun r s t => -allocationsCorrection r s t) X
def conditionalEnergy (X : Finset E4) : ℝ :=
  radialEnergy 0 conditionalLinear (fun r s _ => conditionalPair r s) X
def countsEnergy (X : Finset E4) : ℝ :=
  radialEnergy countOriginQ countsLinear (fun r s _ => countsPair r s) X
def sphericalEnergy (X : Finset E4) : ℝ :=
  radialEnergy 0 sphericalLinear sphericalPair X
def graphsEnergy (X : Finset E4) : ℝ :=
  radialEnergy graphOriginQ (fun _ => 0) (fun r s t => -graphsCorrection r s t) X
def gaugeEnergy (X : Finset E4) : ℝ :=
  radialEnergy 0 (fun r => gaugeWeight r/2)
    (fun r s _ => -(gaugeWeight r*gaugePsi s + gaugeWeight s*gaugePsi r)/2) X

theorem kernel_on_support {x y : E4}
    (hx1 : 1 ≤ ‖x‖) (hxR : ‖x‖ ≤ 7/4) (hy1 : 1 ≤ ‖y‖) (hyR : ‖y‖ ≤ 7/4) :
    kernel x y = pair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)) := by
  have hx : x ≠ 0 := by intro h; subst x; norm_num at hx1
  have hy : y ≠ 0 := by intro h; subst y; norm_num at hy1
  simp only [kernel, if_neg (not_or.mpr ⟨not_lt.mpr hxR, not_lt.mpr hyR⟩),
    if_neg hx, if_neg hy, if_pos (And.intro hx1 hy1)]

theorem kernel_energy_coordinates (X : Finset E4)
    (hX : ∀ x ∈ X, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 7/4) :
    nbhdEnergy kernel X = radialEnergy rawOriginQ linear pair X := by
  have h1 : ∑ x ∈ X, kernel x 0 = ∑ x ∈ X, linear ‖x‖ :=
    Finset.sum_congr rfl fun x hx => kernel_zero_right (hX x hx).1 (hX x hx).2
  have h2 : ∑ x ∈ X, ∑ y ∈ X, kernel x y =
      ∑ x ∈ X, ∑ y ∈ X, pair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)) :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy =>
      kernel_on_support (hX x hx).1 (hX x hx).2 (hX y hy).1 (hX y hy).2
  rw [nbhdEnergy, kernel_origin, h1, h2]
  rfl

/-- Exact decomposition into the nine groups of concrete component energies. -/
theorem energy_decomposition (X : Finset E4)
    (hX : ∀ x ∈ X, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 7/4) :
    nbhdEnergy kernel X = gramEnergy X + capsEnergy X + tentsEnergy X +
      allocationsEnergy X + conditionalEnergy X + countsEnergy X +
      sphericalEnergy X + graphsEnergy X + gaugeEnergy X := by
  rw [kernel_energy_coordinates X hX]
  unfold gramEnergy capsEnergy tentsEnergy allocationsEnergy conditionalEnergy
    countsEnergy sphericalEnergy graphsEnergy gaugeEnergy radialEnergy
  unfold linear pair rawLinear rawPair rawOriginQ capsLinear tentsLinear allocationsLinear
    sphericalLinear conditionalLinear countsLinear countsPair countOriginQ graphOriginQ
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero, Rat.cast_add, neg_div]
  ring

theorem gauge_psi_lt_one (r : ℝ) : gaugePsi r < 1 := by
  unfold gaugePsi indicator gaugeCount
  split_ifs <;> norm_num

theorem gauge_weight_nonneg {r : ℝ} (hq : ungaugedPair r ≤ 0) : 0 ≤ gaugeWeight r := by
  exact div_nonneg (neg_nonneg.mpr hq) (le_of_lt (sub_pos.mpr (gauge_psi_lt_one r)))

theorem gauge_energy_identity (X : Finset E4) (hX : (0 : E4) ∉ X) :
    gaugeEnergy X = (∑ x ∈ X, gaugeWeight ‖x‖) * (1 - ∑ x ∈ X, gaugePsi ‖x‖) := by
  let q := fun x : E4 => ungaugedPair ‖x‖
  let ψ := fun x : E4 => gaugePsi ‖x‖
  have hn : ∀ x ∈ X, x ≠ 0 := fun x hx he => hX (he ▸ hx)
  have hw : ∀ x : E4, Components.gaugeWeight q ψ x = gaugeWeight ‖x‖ := fun _ => rfl
  have h0 : Components.gaugeKernel q ψ 0 0 = 0 := by
    simp [Components.gaugeKernel, Components.usageKernel]
  have h1 : ∑ x ∈ X, Components.gaugeKernel q ψ x 0 = ∑ x ∈ X, gaugeWeight ‖x‖/2 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp [Components.gaugeKernel, Components.usageKernel, hn x hx, hw]
  have h2 : ∑ x ∈ X, ∑ y ∈ X, Components.gaugeKernel q ψ x y =
      ∑ x ∈ X, ∑ y ∈ X, -(gaugeWeight ‖x‖*gaugePsi ‖y‖ + gaugeWeight ‖y‖*gaugePsi ‖x‖)/2 := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    simp [Components.gaugeKernel, Components.usageKernel, hn x hx, hn y hy, hw, ψ]
    ring
  have h := Components.gauge_energy_eq q ψ X hX
  rw [Components.anchoredEnergy, h0, h1, h2] at h
  simpa only [hw, ψ, gaugeEnergy, radialEnergy] using h

theorem gauge_sum_le_one (X : Finset E4) (hcount : countWithin X R3 ≤ 24) :
    ∑ x ∈ X, gaugePsi ‖x‖ ≤ 1 := by
  have he : ∀ x : E4, gaugePsi ‖x‖ = Components.countGauge (50379/50000) 24 x := by
    intro x
    unfold gaugePsi indicator gaugeRadius gaugeCount Components.countGauge
    norm_num
    split_ifs <;> norm_num
  simp_rw [he]
  apply Components.countGauge_sum_le_one _ 24 (by norm_num) X
  convert hcount using 1 <;> norm_num [countWithin, R3]

/-- The actual V7 gauge is nonnegative once its two genuine inputs hold. -/
theorem gauge_energy_nonneg (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hq : ∀ x ∈ X, ungaugedPair ‖x‖ ≤ 0) (hcount : countWithin X R3 ≤ 24) :
    0 ≤ gaugeEnergy X := by
  rw [gauge_energy_identity X hX]
  exact mul_nonneg (Finset.sum_nonneg fun x hx => gauge_weight_nonneg (hq x hx))
    (sub_nonneg.mpr (gauge_sum_le_one X hcount))

end
end D4Bound.V7
