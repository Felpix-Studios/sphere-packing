import D4Bound.V7Gram

/-! Energy decomposition of the actual harmonic Gram rays. Origin equations are
kept explicit so that exact rational projection witnesses can discharge them. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

def gramRayEnergy (ell : ℕ) (ray : Ray) (X : Finset E4) : ℝ :=
  ∑ x ∈ X, ∑ y ∈ X, (ray.weight : ℝ)/(gramDenominator : ℝ) *
    radialValue ray.vector ‖x‖ * radialValue ray.vector ‖y‖ *
      zonal ell (⟪x,y⟫/(‖x‖*‖y‖))

def gramBlockEnergy (ell : ℕ) (X : Finset E4) : ℝ :=
  ((gramRays.getD ell []).map fun ray => gramRayEnergy ell ray X).sum

theorem gramBlock_pair_expand (L : List Ray) (ell : ℕ) (r s t : ℝ) :
    zonal ell t * (L.map fun ray =>
      (ray.weight : ℝ)*radialValue ray.vector r*radialValue ray.vector s).sum /
        (gramDenominator : ℝ) =
    (L.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ) *
      radialValue ray.vector r*radialValue ray.vector s*zonal ell t).sum := by
  induction L with
  | nil => simp
  | cons ray L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [mul_add,add_div,ih]
    ring

theorem gram_pair_energy (X : Finset E4) :
    (∑ x ∈ X, ∑ y ∈ X, gramPair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖))) =
      ((List.range gramRays.length).map fun ell => gramBlockEnergy ell X).sum := by
  unfold gramPair gramBlockEnergy gramRayEnergy
  simp_rw [gramBlock_pair_expand,sum_list_map]

theorem gramDenominator_pos : (0 : ℝ) < (gramDenominator : ℝ) := by
  norm_num [gramDenominator]

theorem gram_weights_nonneg : ∀ L ∈ gramRays, ∀ ray ∈ L, (0 : ℚ) ≤ ray.weight := by
  decide +kernel

theorem property_getD {α : Type*} (P : α → Prop) (L : List α) (d : α)
    (hL : ∀ a ∈ L, P a) (hd : P d) (n : ℕ) : P (L.getD n d) := by
  induction L generalizing n with
  | nil => simpa using hd
  | cons a L ih =>
    cases n with
    | zero => exact hL a (by simp)
    | succ n => exact ih (fun b hb => hL b (by simp [hb])) n

theorem gramRayEnergy_nonneg (ell : ℕ) (ray : Ray) (hw : (0 : ℚ) ≤ ray.weight)
    (X : Finset E4) (hX : (0 : E4) ∉ X) : 0 ≤ gramRayEnergy ell ray X := by
  have h := mul_nonneg
    (div_nonneg (Rat.cast_nonneg.mpr hw) gramDenominator_pos.le)
    (zonal_posDef ell X hX (fun x => radialValue ray.vector ‖x‖))
  have he : gramRayEnergy ell ray X =
      (ray.weight : ℝ)/(gramDenominator : ℝ) *
        (∑ x ∈ X, ∑ y ∈ X, radialValue ray.vector ‖x‖ * radialValue ray.vector ‖y‖ *
          zonal ell (⟪x,y⟫/(‖x‖*‖y‖))) := by
    simp only [gramRayEnergy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [he]
  exact h

theorem gramBlockEnergy_nonneg (ell : ℕ) (X : Finset E4) (hX : (0 : E4) ∉ X) :
    0 ≤ gramBlockEnergy ell X := by
  have hw : ∀ ray ∈ gramRays.getD ell [], (0 : ℚ) ≤ ray.weight :=
    property_getD (fun L => ∀ ray ∈ L, (0 : ℚ) ≤ ray.weight) gramRays []
      gram_weights_nonneg (by simp) ell
  apply List.sum_nonneg
  intro a ha
  obtain ⟨ray,hr,rfl⟩ := List.mem_map.mp ha
  exact gramRayEnergy_nonneg ell ray (hw ray hr) X hX

theorem gram_pair_energy_ge_zero (X : Finset E4) (hX : (0 : E4) ∉ X) :
    gramBlockEnergy 0 X ≤ ∑ x ∈ X, ∑ y ∈ X,
      gramPair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)) := by
  rw [gram_pair_energy]
  apply List.single_le_sum
  · intro a ha
    obtain ⟨ell,hl,rfl⟩ := List.mem_map.mp ha
    exact gramBlockEnergy_nonneg ell X hX
  · exact List.mem_map.mpr ⟨0,by norm_num [gramRays],rfl⟩

theorem gramRayEnergy_zero (ray : Ray) (X : Finset E4) :
    gramRayEnergy 0 ray X = (ray.weight : ℝ)/(gramDenominator : ℝ) *
      (∑ x ∈ X, radialValue ray.vector ‖x‖)^2 := by
  simp only [gramRayEnergy,zonal,chebU,Nat.cast_zero,zero_add,div_one,mul_one]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem gram_zero_square_identity (L : List Ray) (u : Ray → ℝ) (X : Finset E4) :
    (L.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (u ray + ∑ x ∈ X, radialValue ray.vector ‖x‖)^2).sum =
    (L.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*(u ray)^2).sum +
      2*(∑ x ∈ X, (L.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
        u ray*radialValue ray.vector ‖x‖).sum) +
      (L.map fun ray => gramRayEnergy 0 ray X).sum := by
  induction L with
  | nil => simp
  | cons ray L ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    rw [ih,gramRayEnergy_zero]
    simp only [← Finset.mul_sum]
    ring

/-- The exact origin row and origin constant suffice to identify the zero-degree
ray squares; higher degrees have nonnegative energy by the proved S3 theorem. -/
theorem gram_energy_ge_ray_squares (u : Ray → ℝ) (X : Finset E4) (hX : (0 : E4) ∉ X)
    (h0 : (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (u ray)^2).sum = (gramOrigin : ℝ))
    (h1 : ∀ x ∈ X, (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      u ray*radialValue ray.vector ‖x‖).sum = radialValue originVector ‖x‖) :
    (gramRays0.map fun ray => (ray.weight : ℝ)/(gramDenominator : ℝ)*
      (u ray + ∑ x ∈ X, radialValue ray.vector ‖x‖)^2).sum ≤ gramEnergy X := by
  rw [gram_zero_square_identity,h0,Finset.sum_congr rfl h1]
  have h := gram_pair_energy_ge_zero X hX
  have he : gramBlockEnergy 0 X = (gramRays0.map fun ray => gramRayEnergy 0 ray X).sum := rfl
  rw [he] at h
  unfold gramEnergy radialEnergy
  linarith

end
end D4Bound.V7
