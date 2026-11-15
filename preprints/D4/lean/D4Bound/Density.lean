import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Unit packings in `ℝ⁴` and their upper density

`E4` is Euclidean 4-space. A unit packing is a set of centres at pairwise distance at least 1,
that is, the centres of non-overlapping balls of radius `1/2`. Its upper density is

  `limsup_{R → ∞} vol(B(1/2)) · #(P ∩ B(0,R)) / vol(B(0,R))`,

taken in `ℝ≥0∞` so that it is always defined. `Transfer.lean` proves that `P ∩ B(0,R)` is
finite for every unit packing, so the count is a natural number.
-/

open MeasureTheory Metric

namespace D4Bound

/-- Euclidean 4-space. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

lemma volume_ball_E4 (x : E4) (r : ℝ) :
    volume (ball x r) = ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  have h := InnerProductSpace.volume_ball_of_dim_even (E := E4) (k := 2) (by simp) x r
  simpa using h

lemma volume_real_ball_E4 (x : E4) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = Real.pi ^ 2 / 2 * r ^ 4 := by
  rw [measureReal_def, volume_ball_E4, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring


/-- Centres pairwise at distance at least 1 (balls of radius 1/2 with disjoint interiors). -/
def IsUnitPacking (P : Set E4) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ dist x y

/-- Upper density: `limsup_{R → ∞} vol(B(1/2)) · #(P ∩ B(0,R)) / vol(B(0,R))`, in `ℝ≥0∞`. -/
noncomputable def upperDensity (P : Set E4) : ENNReal :=
  Filter.limsup (fun R : ℝ => volume (ball (0 : E4) (1 / 2)) *
    ((P ∩ ball (0 : E4) R).encard : ENNReal) / volume (ball (0 : E4) R)) Filter.atTop


end D4Bound
