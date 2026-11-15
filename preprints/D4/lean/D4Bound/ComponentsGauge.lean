import D4Bound.ComponentsGram

/-!
# Component lemmas: capacity-minus-usage energies and the pair count gauge

Several V7 components have the form "capacity minus usage":

  `E(X) = ∑_{y∈X} u(y) (1 - ∑_{x∈X} cap(y, x))`,

with `u ≥ 0` and `∑_{x∈X} cap(y, x) ≤ 1` for every `y`. Its symmetric kernel encoding has
origin constant `0`, origin coupling `K(x,0) = u(x)/2` and
`K(x,y) = -(u(y) cap(y,x) + u(x) cap(x,y))/2` (`usageKernel`). `usage_energy_eq` proves that
the anchored energy of this kernel is exactly `E(X)`, and `usage_energy_nonneg` that it is `≥ 0`.

The pair count gauge (`COMPONENTS.md` row 15, paper Section 3 item 6,
`proofs/current/base/new_work/copositive/ADAPTIVE_COUNT_GAUGES.md` section 1) is the case
`cap(y,x) = ψ(x)`, `u = w = -q/(1-ψ)`. Then `E = (∑ w)(1 - ∑ ψ)` (`gauge_energy_eq`), and its pair
term is `2K(x,0) + K(x,x) = w(x)(1 - ψ(x)) = -q(x)` (`gauge_pair_term`). With
`ψ(x) = 1[|x| ≤ R₃]/24` the condition `∑ ψ ≤ 1` is the count bound `n₃ ≤ 24`
(`countGauge_sum_le_one`), which is the spherical-code count of row 8 and is a hypothesis here.
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound
namespace Components

/-- Kernel of the energy `∑_y u(y) (1 - ∑_x cap(y,x))`. -/
noncomputable def usageKernel (u : R4 → ℝ) (cap : R4 → R4 → ℝ) (x y : R4) : ℝ :=
  if x = 0 then (if y = 0 then 0 else u y / 2)
  else if y = 0 then u x / 2 else -(u y * cap y x + u x * cap x y) / 2

/-- The anchored energy of `usageKernel` is `∑_y u(y) (1 - ∑_x cap(y,x))`. -/
theorem usage_energy_eq (u : R4 → ℝ) (cap : R4 → R4 → ℝ) (X : Finset R4) (hX : (0 : R4) ∉ X) :
    anchoredEnergy (usageKernel u cap) X = ∑ y ∈ X, u y * (1 - ∑ x ∈ X, cap y x) := by
  have hne : ∀ x ∈ X, x ≠ 0 := fun x hx h => hX (h ▸ hx)
  have h1 : ∑ x ∈ X, usageKernel u cap x 0 = ∑ x ∈ X, u x / 2 :=
    Finset.sum_congr rfl fun x hx => by simp [usageKernel, hne x hx]
  have h2 : ∑ x ∈ X, ∑ y ∈ X, usageKernel u cap x y =
      ∑ x ∈ X, ∑ y ∈ X, -(u y * cap y x + u x * cap x y) / 2 :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
      simp [usageKernel, hne x hx, hne y hy]
  have h3 : ∑ x ∈ X, ∑ y ∈ X, u y * cap y x = ∑ x ∈ X, ∑ y ∈ X, u x * cap x y :=
    Finset.sum_comm
  have h4 : ∑ x ∈ X, ∑ y ∈ X, -(u y * cap y x + u x * cap x y) / 2 =
      -∑ x ∈ X, ∑ y ∈ X, u x * cap x y := by
    simp only [neg_div, Finset.sum_neg_distrib, add_div, Finset.sum_add_distrib,
      ← Finset.sum_div]
    rw [h3]
    ring
  have h5 : usageKernel u cap 0 0 = 0 := by simp [usageKernel]
  rw [anchoredEnergy, h1, h2, h4, h5, Finset.mul_sum]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
  have h6 : ∑ x ∈ X, 2 * (u x / 2) = ∑ x ∈ X, u x :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [h6]
  ring

/-- **Capacity minus usage.** If `u ≥ 0` on `X` and `∑_{x∈X} cap(y,x) ≤ 1` for every `y ∈ X`,
the energy is `≥ 0`. -/
theorem usage_energy_nonneg (u : R4 → ℝ) (cap : R4 → R4 → ℝ) (X : Finset R4)
    (hX : (0 : R4) ∉ X) (hu : ∀ y ∈ X, 0 ≤ u y) (hcap : ∀ y ∈ X, ∑ x ∈ X, cap y x ≤ 1) :
    0 ≤ anchoredEnergy (usageKernel u cap) X := by
  rw [usage_energy_eq u cap X hX]
  exact Finset.sum_nonneg fun y hy => mul_nonneg (hu y hy) (by linarith [hcap y hy])

/-- Pair term of a usage kernel: `2K(x,0) + K(x,x) = u(x)(1 - cap(x,x))`. -/
lemma usage_pair_term (u : R4 → ℝ) (cap : R4 → R4 → ℝ) {x : R4} (hx : x ≠ 0) :
    2 * usageKernel u cap x 0 + usageKernel u cap x x = u x * (1 - cap x x) := by
  simp [usageKernel, hx]
  ring

/-! ## The pair count gauge -/

/-- Gauge weight `w = -q/(1-ψ)`. -/
noncomputable def gaugeWeight (q ψ : R4 → ℝ) (x : R4) : ℝ := -q x / (1 - ψ x)

/-- The gauge kernel: `cap(y,x) = ψ(x)` and `u = w`. -/
noncomputable def gaugeKernel (q ψ : R4 → ℝ) : R4 → R4 → ℝ :=
  usageKernel (gaugeWeight q ψ) (fun _ x => ψ x)

/-- **Row 15, energy.** `E(X) = (∑_X w)(1 - ∑_X ψ)`. -/
theorem gauge_energy_eq (q ψ : R4 → ℝ) (X : Finset R4) (hX : (0 : R4) ∉ X) :
    anchoredEnergy (gaugeKernel q ψ) X =
      (∑ x ∈ X, gaugeWeight q ψ x) * (1 - ∑ x ∈ X, ψ x) := by
  rw [gaugeKernel, usage_energy_eq _ _ X hX, Finset.sum_mul]

/-- **Row 15, sign.** If `q ≤ 0` and `ψ < 1` on `X`, and `∑_X ψ ≤ 1`, the gauge energy is `≥ 0`. -/
theorem gauge_energy_nonneg (q ψ : R4 → ℝ) (X : Finset R4) (hX : (0 : R4) ∉ X)
    (hq : ∀ x ∈ X, q x ≤ 0) (hψ : ∀ x ∈ X, ψ x < 1) (hsum : ∑ x ∈ X, ψ x ≤ 1) :
    0 ≤ anchoredEnergy (gaugeKernel q ψ) X := by
  refine usage_energy_nonneg _ _ X hX (fun y hy => ?_) (fun _ _ => hsum)
  exact div_nonneg (by linarith [hq y hy]) (by linarith [hψ y hy])

/-- **Row 15, pair term.** `2K(x,0) + K(x,x) = w(x)(1 - ψ(x)) = -q(x)` when `ψ(x) ≠ 1`, so adding
the gauge makes the pair term of the full kernel `q + (-q) = 0`. -/
theorem gauge_pair_term (q ψ : R4 → ℝ) {x : R4} (hx : x ≠ 0) (hψ : ψ x ≠ 1) :
    2 * gaugeKernel q ψ x 0 + gaugeKernel q ψ x x = -q x := by
  rw [gaugeKernel, usage_pair_term _ _ hx, gaugeWeight]
  have : 1 - ψ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hψ)
  field_simp

/-- The count gauge `ψ(x) = 1[|x| ≤ R]/N`. -/
noncomputable def countGauge (R : ℝ) (N : ℕ) (x : R4) : ℝ := if ‖x‖ ≤ R then 1 / N else 0

/-- `∑_X ψ ≤ 1` iff at most `N` points of `X` lie within `R`; here the direction used. -/
theorem countGauge_sum_le_one (R : ℝ) (N : ℕ) (hN : 0 < N) (X : Finset R4)
    (hcount : (X.filter fun x => ‖x‖ ≤ R).card ≤ N) :
    ∑ x ∈ X, countGauge R N x ≤ 1 := by
  classical
  have : ∑ x ∈ X, countGauge R N x = (X.filter fun x => ‖x‖ ≤ R).card / (N : ℝ) := by
    unfold countGauge
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [this, div_le_one (by exact_mod_cast hN)]
  exact_mod_cast hcount

lemma countGauge_lt_one (R : ℝ) {N : ℕ} (hN : 1 < N) (x : R4) : countGauge R N x < 1 := by
  unfold countGauge
  split_ifs
  · rw [div_lt_one (by positivity)]; exact_mod_cast hN
  · norm_num

/-- **Row 15 with the base certificate's gauge** `ψ = 1[|x| ≤ R₃]/24`, `R₃ = 50379/50000`.
If `q ≤ 0` on `X` and `X` has at most `24` points within `R₃` (the count of row 8, assumed here),
the gauge energy is `≥ 0`. -/
theorem pair_count_gauge_nonneg (q : R4 → ℝ) (X : Finset R4) (hX : (0 : R4) ∉ X)
    (hq : ∀ x ∈ X, q x ≤ 0)
    (hcount : (X.filter fun x => ‖x‖ ≤ (50379 / 50000 : ℝ)).card ≤ 24) :
    0 ≤ anchoredEnergy (gaugeKernel q (countGauge (50379 / 50000) 24)) X :=
  gauge_energy_nonneg q _ X hX hq (fun x _ => countGauge_lt_one _ (by norm_num) x)
    (countGauge_sum_le_one _ 24 (by norm_num) X hcount)

end Components
end D4Bound
