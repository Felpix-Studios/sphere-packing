import D4Bound.SchoenbergS3

/-!
# Component lemmas: the harmonic Gram kernel and the origin credit

`COMPONENTS.md` rows 1 (harmonic Gram kernel with origin row), 2 (Broad19 rays, which are
rays of row 1) and 16 (origin credit) of `verify/stage1_v7`.

A *ray* `i` has a degree `deg i`, a weight `w i ≥ 0` and an integer (here: real) vector `v i` in
the radial feature space `ℝᵐ`. The degree-`l` Gram block is `M_l = ∑_{deg i = l} w i v i v iᵀ`.
With a radial feature map `φ : ℝ → ℝᵐ` and an origin vector `u`, the kernel is

  `K(x,y) = ∑_l φ(|x|)ᵀ M_l φ(|y|) Z_l(⟪x,y⟫/(|x||y|))`     for `x, y ≠ 0`,
  `K(x,0) = φ(|x|)ᵀ M₀ u`,   `K(0,0) = uᵀ M₀ u`,

with `Z_l = U_l/(l+1)`. Equivalently, the origin carries the feature `u` in block `0` and the
feature `0` in the other blocks; this is the "origin coordinate convention" of the paper
(Section 3, item 1), where `M₀ u = v_origin` and `uᵀ M₀ u = κ`.

`gram_energy_nonneg`: the anchored energy `K(0,0) + 2∑ K(x,0) + ∑∑ K(x,y)` is `≥ 0` on every
finite set of nonzero points. It uses Schoenberg's theorem for `S³` (`schoenberg_S3`, proved in
`SchoenbergS3.lean`) and needs no separation or radius assumption.

`gram_origin_credit`: for any vector `b`, with `a = M₀ b` and `g = 2 u·a - a·b`,
`E_u(X) - g = E_{u-b}(X) + 2 ∑_{x∈X} a·φ(|x|)`; so `E_u(X) ≥ g` when `a·φ(r) ≥ 0` on the radii
of `X` (`COMPONENTS.md` row 16, `proofs/audit/ORIGIN_CREDIT_THEOREM.md`).
`origin_credit_identity` is the same completed square for an arbitrary symmetric matrix.
-/

open Finset Matrix
open scoped RealInnerProductSpace

namespace D4Bound
namespace Components

/-- Points of `ℝ⁴`. -/
abbrev R4 := EuclideanSpace ℝ (Fin 4)

/-- The anchored energy `E_K(X) = K(0,0) + 2 ∑_{x∈X} K(x,0) + ∑_{x,y∈X} K(x,y)`.
It is the same expression as `nbhdEnergy` in `Neighbourhood.lean`. -/
noncomputable def anchoredEnergy (K : R4 → R4 → ℝ) (X : Finset R4) : ℝ :=
  K 0 0 + 2 * ∑ x ∈ X, K x 0 + ∑ x ∈ X, ∑ y ∈ X, K x y

/-- `Z_l(t) = U_l(t)/(l+1)`, the Gegenbauer polynomial of parameter `1` normalized by `Z_l(1) = 1`. -/
noncomputable def zfun (l : ℕ) (t : ℝ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (l : ℤ)).eval t / ((l : ℝ) + 1)

lemma zfun_zero (t : ℝ) : zfun 0 t = 1 := by simp [zfun]

/-- Rays of a harmonic Gram kernel. -/
structure GramRays (ι : Type*) (m : ℕ) where
  /-- The finite set of rays. -/
  rays : Finset ι
  /-- Harmonic degree of each ray. -/
  deg : ι → ℕ
  /-- Weight of each ray. -/
  w : ι → ℝ
  /-- Vector of each ray in the feature space. -/
  v : ι → Fin m → ℝ

variable {ι : Type*} {m : ℕ}

/-- Feature coordinate of a point for ray `i`: `v i · φ(|x|)` for `x ≠ 0`; at the origin,
`v i · u` in degree `0` and `0` in the other degrees. -/
noncomputable def coord (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ) (i : ι)
    (x : R4) : ℝ :=
  if x = 0 then (if G.deg i = 0 then G.v i ⬝ᵥ u else 0) else G.v i ⬝ᵥ φ ‖x‖

/-- Angular factor of ray `i`: `Z_{deg i}(⟪x,y⟫/(|x||y|))`, and `1` if a point is the origin. -/
noncomputable def ang (G : GramRays ι m) (i : ι) (x y : R4) : ℝ :=
  if x = 0 ∨ y = 0 then 1 else zfun (G.deg i) (⟪x, y⟫ / (‖x‖ * ‖y‖))

/-- The harmonic Gram kernel with origin row. -/
noncomputable def gramKernel (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ)
    (x y : R4) : ℝ :=
  ∑ i ∈ G.rays, G.w i * coord G φ u i x * coord G φ u i y * ang G i x y

/-- Degree-`l` Gram block `M_l = ∑_{deg i = l} w i v i v iᵀ`. -/
noncomputable def block (G : GramRays ι m) (l : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i ∈ G.rays.filter (fun i => G.deg i = l), G.w i • vecMulVec (G.v i) (G.v i)

lemma dot_vecMulVec (v a b : Fin m → ℝ) :
    a ⬝ᵥ (vecMulVec v v *ᵥ b) = (v ⬝ᵥ a) * (v ⬝ᵥ b) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma dot_block_dot (G : GramRays ι m) (l : ℕ) (a b : Fin m → ℝ) :
    a ⬝ᵥ (block G l *ᵥ b) =
      ∑ i ∈ G.rays.filter (fun i => G.deg i = l), G.w i * (G.v i ⬝ᵥ a) * (G.v i ⬝ᵥ b) := by
  simp only [block, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul, dot_vecMulVec]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- For `x, y ≠ 0` the kernel is `∑_l φ(|x|)ᵀ M_l φ(|y|) Z_l(cos)`, summed over the degrees of
the rays (the paper's formula). -/
lemma gramKernel_eq_blocks [DecidableEq ι] (G : GramRays ι m) (φ : ℝ → Fin m → ℝ)
    (u : Fin m → ℝ) {x y : R4} (hx : x ≠ 0) (hy : y ≠ 0) :
    gramKernel G φ u x y = ∑ l ∈ G.rays.image G.deg,
      φ ‖x‖ ⬝ᵥ (block G l *ᵥ φ ‖y‖) * zfun l (⟪x, y⟫ / (‖x‖ * ‖y‖)) := by
  simp only [dot_block_dot, Finset.sum_mul]
  rw [gramKernel, ← Finset.sum_fiberwise_of_maps_to (g := G.deg)
    (fun i hi => Finset.mem_image_of_mem G.deg hi)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i hi => ?_
  have hl : G.deg i = l := (Finset.mem_filter.mp hi).2
  simp [coord, ang, hx, hy, hl]

lemma gramKernel_zero_zero (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ) :
    gramKernel G φ u 0 0 = u ⬝ᵥ (block G 0 *ᵥ u) := by
  rw [dot_block_dot, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : G.deg i = 0 <;> simp [coord, ang, h]

lemma gramKernel_x_zero (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ) {x : R4}
    (hx : x ≠ 0) : gramKernel G φ u x 0 = φ ‖x‖ ⬝ᵥ (block G 0 *ᵥ u) := by
  rw [dot_block_dot, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : G.deg i = 0 <;> simp [coord, ang, h, hx]

/-- Energy of one ray. -/
noncomputable def rayEnergy (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ) (i : ι)
    (X : Finset R4) : ℝ :=
  coord G φ u i 0 * coord G φ u i 0 * ang G i 0 0 +
    2 * ∑ x ∈ X, coord G φ u i x * coord G φ u i 0 * ang G i x 0 +
    ∑ x ∈ X, ∑ y ∈ X, coord G φ u i x * coord G φ u i y * ang G i x y

lemma energy_eq_sum_rays (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ)
    (X : Finset R4) :
    anchoredEnergy (gramKernel G φ u) X = ∑ i ∈ G.rays, G.w i * rayEnergy G φ u i X := by
  set c := coord G φ u
  have h1 : gramKernel G φ u 0 0 = ∑ i ∈ G.rays, G.w i * (c i 0 * c i 0 * ang G i 0 0) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ x ∈ X, gramKernel G φ u x 0 =
      ∑ i ∈ G.rays, G.w i * ∑ x ∈ X, c i x * c i 0 * ang G i x 0 := by
    unfold gramKernel
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h3 : ∑ x ∈ X, ∑ y ∈ X, gramKernel G φ u x y =
      ∑ i ∈ G.rays, G.w i * ∑ x ∈ X, ∑ y ∈ X, c i x * c i y * ang G i x y := by
    unfold gramKernel
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [anchoredEnergy, h1, h2, h3, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [rayEnergy]
  ring

/-- Positive definiteness of `Z_l(cos)` on finitely many nonzero points of `ℝ⁴`. -/
lemma zfun_posDef (l : ℕ) (X : Finset R4) (hX : (0 : R4) ∉ X) (c : R4 → ℝ) :
    0 ≤ ∑ x ∈ X, ∑ y ∈ X, c x * c y * zfun l (⟪x, y⟫ / (‖x‖ * ‖y‖)) := by
  have hne : ∀ x ∈ X, x ≠ 0 := fun x hx h => hX (h ▸ hx)
  have hS := schoenberg_S3 l R4 X (fun x => ‖x‖⁻¹ • x) c
    (fun x hx => norm_smul_inv_norm (hne x hx))
  have key : ∑ x ∈ X, ∑ y ∈ X, c x * c y * zfun l (⟪x, y⟫ / (‖x‖ * ‖y‖)) =
      (∑ x ∈ X, ∑ y ∈ X, c x * c y *
        (Polynomial.Chebyshev.U ℝ (l : ℤ)).eval ⟪‖x‖⁻¹ • x, ‖y‖⁻¹ • y⟫) / ((l : ℝ) + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [zfun, real_inner_smul_left, real_inner_smul_right]
    have : ‖x‖⁻¹ * (‖y‖⁻¹ * ⟪x, y⟫) = ⟪x, y⟫ / (‖x‖ * ‖y‖) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [this]
    ring
  rw [key]
  positivity

lemma rayEnergy_nonneg (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ) (i : ι)
    (X : Finset R4) (hX : (0 : R4) ∉ X) : 0 ≤ rayEnergy G φ u i X := by
  have hne : ∀ x ∈ X, x ≠ 0 := fun x hx h => hX (h ▸ hx)
  by_cases hd : G.deg i = 0
  · -- degree 0: the energy is a square
    have hang : ∀ x y, ang G i x y = 1 := fun x y => by
      by_cases h : x = 0 ∨ y = 0 <;> simp [ang, h, hd, zfun_zero]
    have : rayEnergy G φ u i X = (coord G φ u i 0 + ∑ x ∈ X, coord G φ u i x) ^ 2 := by
      simp only [rayEnergy, hang, mul_one]
      rw [← Finset.sum_mul, ← Finset.sum_mul_sum]
      ring
    rw [this]
    positivity
  · have h0 : coord G φ u i 0 = 0 := by simp [coord, hd]
    simp only [rayEnergy, h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    have hS := zfun_posDef (G.deg i) X hX (fun x => coord G φ u i x)
    convert hS using 1
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    simp [ang, hne x hx, hne y hy]

/-- **Row 1.** The harmonic Gram kernel with origin row has nonnegative anchored energy on every
finite set of nonzero points, when every ray weight is nonnegative. -/
theorem gram_energy_nonneg (G : GramRays ι m) (hw : ∀ i ∈ G.rays, 0 ≤ G.w i)
    (φ : ℝ → Fin m → ℝ) (u : Fin m → ℝ) (X : Finset R4) (hX : (0 : R4) ∉ X) :
    0 ≤ anchoredEnergy (gramKernel G φ u) X := by
  rw [energy_eq_sum_rays]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (rayEnergy_nonneg G φ u i X hX)

/-! ## The origin credit -/

/-- **Row 16, matrix form.** For a symmetric matrix `M` with `M b = a` and `g = 2 u·a - a·b`,
`(u+z)ᵀ M (u+z) - g = (u-b+z)ᵀ M (u-b+z) + 2 a·z`. -/
theorem origin_credit_identity {n : Type*} [Fintype n] (M : Matrix n n ℝ) (hM : Mᵀ = M)
    (u b z a : n → ℝ) (hb : M *ᵥ b = a) :
    (u + z) ⬝ᵥ (M *ᵥ (u + z)) - (2 * (u ⬝ᵥ a) - a ⬝ᵥ b) =
      (u - b + z) ⬝ᵥ (M *ᵥ (u - b + z)) + 2 * (a ⬝ᵥ z) := by
  have hsym : ∀ p q : n → ℝ, p ⬝ᵥ (M *ᵥ q) = q ⬝ᵥ (M *ᵥ p) := by
    intro p q
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  have e1 : (u - b + z) = (u + z) - b := by abel
  rw [e1, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hsym b (u + z), hb]
  simp only [add_dotProduct, dotProduct_comm a]
  ring

/-- With `b`, the credit weight `a·φ(r)` where `a = M₀ b`. -/
noncomputable def creditWeight (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (b : Fin m → ℝ)
    (r : ℝ) : ℝ :=
  φ r ⬝ᵥ (block G 0 *ᵥ b)

/-- The origin credit `g = 2 u·a - a·b` with `a = M₀ b`. -/
noncomputable def credit (G : GramRays ι m) (u b : Fin m → ℝ) : ℝ :=
  2 * (u ⬝ᵥ (block G 0 *ᵥ b)) - (block G 0 *ᵥ b) ⬝ᵥ b

lemma block_transpose (G : GramRays ι m) (l : ℕ) : (block G l)ᵀ = block G l := by
  simp [block, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

/-- **Row 16.** `E_u(X) - g = E_{u-b}(X) + 2 ∑_{x∈X} a·φ(|x|)` with `a = M₀ b`,
`g = 2 u·a - a·b`. The kernel off the origin does not depend on `u`. -/
theorem gram_origin_credit (G : GramRays ι m) (φ : ℝ → Fin m → ℝ) (u b : Fin m → ℝ)
    (X : Finset R4) (hX : (0 : R4) ∉ X) :
    anchoredEnergy (gramKernel G φ u) X - credit G u b =
      anchoredEnergy (gramKernel G φ (u - b)) X + 2 * ∑ x ∈ X, creditWeight G φ b ‖x‖ := by
  have hne : ∀ x ∈ X, x ≠ 0 := fun x hx h => hX (h ▸ hx)
  set M := block G 0
  set z : Fin m → ℝ := ∑ x ∈ X, φ ‖x‖
  -- the part of the energy that depends on the origin vector
  have hsplit : ∀ u' : Fin m → ℝ, anchoredEnergy (gramKernel G φ u') X =
      (u' + z) ⬝ᵥ (M *ᵥ (u' + z)) - z ⬝ᵥ (M *ᵥ z) +
        ∑ x ∈ X, ∑ y ∈ X, gramKernel G φ 0 x y := by
    intro u'
    have hxy : ∀ x ∈ X, ∀ y ∈ X, gramKernel G φ u' x y = gramKernel G φ 0 x y := by
      intro x hx y hy
      simp [gramKernel, coord, hne x hx, hne y hy]
    have hx0 : ∑ x ∈ X, gramKernel G φ u' x 0 = z ⬝ᵥ (M *ᵥ u') := by
      rw [Finset.sum_congr rfl fun x hx => gramKernel_x_zero G φ u' (hne x hx)]
      simp only [z, sum_dotProduct]
      rfl
    have hsym : z ⬝ᵥ (M *ᵥ u') = u' ⬝ᵥ (M *ᵥ z) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, block_transpose, dotProduct_comm]
    rw [anchoredEnergy, gramKernel_zero_zero, hx0,
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hxy x hx y hy]
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    rw [hsym]
    ring
  have hc : ∑ x ∈ X, creditWeight G φ b ‖x‖ = (M *ᵥ b) ⬝ᵥ z := by
    simp only [creditWeight, z, sum_dotProduct, dotProduct_comm (M *ᵥ b)]
    rfl
  rw [hsplit u, hsplit (u - b), hc, credit]
  have := origin_credit_identity M (block_transpose G 0) u b z (M *ᵥ b) rfl
  linarith

/-- **Row 16, consequence.** If `a·φ(r) ≥ 0` at the radii of `X` (with `a = M₀ b`) and the ray
weights are nonnegative, then `E_u(X) ≥ g`. -/
theorem gram_energy_ge_credit (G : GramRays ι m) (hw : ∀ i ∈ G.rays, 0 ≤ G.w i)
    (φ : ℝ → Fin m → ℝ) (u b : Fin m → ℝ) (X : Finset R4) (hX : (0 : R4) ∉ X)
    (hcw : ∀ x ∈ X, 0 ≤ creditWeight G φ b ‖x‖) :
    credit G u b ≤ anchoredEnergy (gramKernel G φ u) X := by
  have h := gram_origin_credit G φ u b X hX
  have h1 := gram_energy_nonneg G hw φ (u - b) X hX
  have h2 : 0 ≤ ∑ x ∈ X, creditWeight G φ b ‖x‖ := Finset.sum_nonneg hcw
  linarith

end Components
end D4Bound
