import D4Bound.V7CensusGramOriginSound
namespace D4Bound.V7.CensusGram
open Finset
noncomputable section
open Classical
set_option maxHeartbeats 0

def planeCentreQ (a : List ℚ) (r : Ray) : ℚ := a.getD (rayIndex r) 0

def planeRowOK (a v : List ℚ) (k : ℕ) : Bool := decide (
  (gramRays0.map fun ray => 2*ray.weight/gramDenominator*planeCentreQ a ray*
    ray.vector.getD k 0).sum = v.getD k 0)

def planeConstantOK (a : List ℚ) (c : ℚ) : Bool := decide (
  (gramRays0.map fun ray => ray.weight/gramDenominator*
    (2*planeCentreQ a ray*originOffsetQ ray-(planeCentreQ a ray)^2)).sum = c)

theorem list_ray_center_bound (L : List Ray) (u z a : Ray → ℝ)
    (hw : ∀ ray ∈ L, 0 ≤ (ray.weight : ℝ)/(gramDenominator : ℝ)) :
    (L.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (2*a ray*u ray-(a ray)^2)).sum +
    (L.map fun ray => 2*(ray.weight : ℝ)/(gramDenominator : ℝ)*a ray*z ray).sum ≤
    (L.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*(u ray+z ray)^2).sum := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have hr := mul_nonneg (hw r (by simp)) (sq_nonneg (u r+z r-a r))
    have ht := ih (fun s hs => hw s (by simp [hs]))
    simp only [List.map_cons,List.sum_cons]
    have he : (r.weight : ℝ)/(gramDenominator : ℝ)*(u r+z r)^2 -
        ((r.weight : ℝ)/(gramDenominator : ℝ)*(2*a r*u r-(a r)^2) +
         2*(r.weight : ℝ)/(gramDenominator : ℝ)*a r*z r) =
        (r.weight : ℝ)/(gramDenominator : ℝ)*(u r+z r-a r)^2 := by ring
    linarith

theorem gram_plane_floor (a v b : List ℚ) (c : ℚ)
    (hc : planeConstantOK a c = true)
    (hv : ∀ k, k < 49 → planeRowOK a v k = true)
    (X : Finset E4) (hX : (0 : E4) ∉ X) (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4)
    (hb : ∀ x ∈ X, ((List.range 5).map fun j =>
      (b.getD j 0 : ℝ)*indicator (breaks.getD (j+1) 0) ‖x‖).sum ≤ radialValue v ‖x‖) :
    (c : ℝ) + ((List.range 5).map fun j => (b.getD j 0 : ℝ)*
      (countWithin X ((breaks.getD (j+1) 0 : ℚ) : ℝ) : ℝ)).sum ≤ gramEnergy X := by
  have hw : ∀ ray ∈ gramRays0, 0 ≤ (ray.weight : ℝ)/(gramDenominator : ℝ) := by
    intro ray hr
    have h := gram_weights_nonneg gramRays0 (by simp [gramRays]) ray hr
    exact div_nonneg (Rat.cast_nonneg.mpr h) gramDenominator_pos.le
  have hs := list_ray_center_bound gramRays0 originOffset
    (fun ray => ∑ x ∈ X, radialValue ray.vector ‖x‖)
    (fun ray => (planeCentreQ a ray : ℝ)) hw
  have hcq : (gramRays0.map fun ray => ray.weight/gramDenominator*
      (2*planeCentreQ a ray*originOffsetQ ray-(planeCentreQ a ray)^2)).sum = c :=
    of_decide_eq_true hc
  have hcr := congrArg (fun q : ℚ => (q : ℝ)) hcq
  rw [cast_list_sum] at hcr
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_ofNat] at hcr
  change (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (2*(planeCentreQ a ray : ℝ)*originOffset ray-(planeCentreQ a ray : ℝ)^2)).sum = _ at hcr
  rw [hcr] at hs
  have hvx : ∀ x ∈ X, (gramRays0.map fun ray =>
      2*(ray.weight : ℝ)/(gramDenominator : ℝ)*(planeCentreQ a ray : ℝ)*
      radialValue ray.vector ‖x‖).sum = radialValue v ‖x‖ := by
    intro x hx
    have h := radialValue_combination gramRays0
      (fun ray => 2*ray.weight/gramDenominator*planeCentreQ a ray) Ray.vector v
      (fun k hk => of_decide_eq_true (hv k hk)) (hR x hx)
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using h
  have he : (gramRays0.map fun ray =>
      2*(ray.weight : ℝ)/(gramDenominator : ℝ)*(planeCentreQ a ray : ℝ)*
      ∑ x ∈ X, radialValue ray.vector ‖x‖).sum = ∑ x ∈ X, radialValue v ‖x‖ := by
    simp_rw [Finset.mul_sum]
    rw [← sum_list_map]
    exact Finset.sum_congr rfl hvx
  rw [he] at hs
  have hf := radial_count_floor v b X hb
  have hg := hs.trans (gram_energy_ge_origin_squares X hX hR)
  linarith
end
end D4Bound.V7.CensusGram
