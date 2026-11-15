import D4Bound.Neighbourhood
import D4Bound.Geometry
import D4Bound.Ledger
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The count domain (Lemma 4.1)

For an admissible neighbourhood `X` let `n_j = #{x ∈ X : ‖x‖ ≤ R_j}`. This file proves
(`countDomain_of_admissible`) that the count vector lies in the domain `C` of the census:

  `n₁ ≤ … ≤ n₅`, `n ≤ (24, 24, 24, 25, 26)`, `(23 - n₁)(n₅ - n₁) ≥ 0`, `(23 - n₂)(n₄ - n₂) ≥ 0`,

and (`group_mem`) that the group `(N, j)` of `X` is one of the 124 groups of the ledger.

Named hypotheses, each the statement an exact checker proves:

* `SphericalCodeBound (203/400) 24`, `SphericalCodeBound (103/200) 25`,
  `SphericalCodeBound (21/40) 26`: the three spherical code bounds of stage 2 (Delsarte
  certificates `s05075_taper12_exact.json`, `s0515_count25_exact.json`,
  `s0525_count26_exact.json`, rechecked by `certify.py`).
* `LatitudeCert R1 R5`, `LatitudeCert R2 R4`: the sign statement over `[-1, c]²` that
  `affine_latitude_counts.py` `check(r, R)` proves by exact Bernstein subdivision.

Proved here: the shell-to-sphere transfer (`Geometry.lean`), the caps, the affine latitude map
and the reduction of Section 3 of `AFFINE_LATITUDE_THEOREM.md` (pairs whose original inner
product cannot reach `s` are moved along a meridian), the 25-point code, monotonicity and the
group bookkeeping.
-/

open Finset Real
open scoped RealInnerProductSpace

namespace D4Bound

/-! ## Affine latitude: scalar part -/

section scalar

/-- The latitude map `φ(a) = α a - β`, `α = 1 - β`. -/
def latPhi (β a : ℝ) : ℝ := (1 - β) * a - β

/-- `k(a)² = α ((1 - a) + β (1 + a)) / (1 - a)`. -/
noncomputable def latK2 (β a : ℝ) : ℝ := (1 - β) * ((1 - a) + β * (1 + a)) / (1 - a)

/-- The perpendicular multiplier `k(a)`. -/
noncomputable def latK (β a : ℝ) : ℝ := √(latK2 β a)

/-- `P = S - φ(a) φ(b)`. -/
def latP (S β a b : ℝ) : ℝ := S - latPhi β a * latPhi β b

/-- `H = P² (1 - a)(1 - b) - α² ((1 - a) + β(1 + a))((1 - b) + β(1 + b)) (s - ab)²`. -/
def latH (s S β a b : ℝ) : ℝ :=
  latP S β a b ^ 2 * ((1 - a) * (1 - b)) -
    (1 - β) ^ 2 * (((1 - a) + β * (1 + a)) * ((1 - b) + β * (1 + b))) * (s - a * b) ^ 2

/-- The sign statement that `affine_latitude_counts.py` proves on `[-1, c]²`: wherever
`D(a, b) = 1 - s² + 2sab - a² - b² ≥ 0`, one of the three sign cases holds, with
`P = S - φ(a)φ(b)`, `V = s - ab` and `H` as in `latH`. -/
def LatSign (s c S β : ℝ) : Prop :=
  ∀ a b : ℝ, -1 ≤ a → a ≤ c → -1 ≤ b → b ≤ c →
    0 ≤ 1 - s ^ 2 + 2 * s * (a * b) - a ^ 2 - b ^ 2 →
    (0 ≤ latP S β a b ∧ s - a * b ≤ 0) ∨ (0 ≤ latP S β a b ∧ 0 ≤ latH s S β a b) ∨
      (s - a * b ≤ 0 ∧ latH s S β a b ≤ 0)

variable {s c S β : ℝ}

lemma latK2_nonneg (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {a : ℝ} (ha : -1 ≤ a) (ha1 : a < 1) :
    0 ≤ latK2 β a := by
  unfold latK2
  apply div_nonneg _ (by linarith)
  apply mul_nonneg (by linarith)
  nlinarith

lemma latK_nonneg (β a : ℝ) : 0 ≤ latK β a := Real.sqrt_nonneg _

/-- `k(a) √(1 - a²) = √(1 - φ(a)²)`. -/
lemma latK_mul_sqrt (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {a : ℝ} (ha : -1 ≤ a) (ha1 : a < 1) :
    latK β a * √(1 - a ^ 2) = √(1 - latPhi β a ^ 2) := by
  rw [latK, ← Real.sqrt_mul (latK2_nonneg hβ0 hβ1 ha ha1)]
  congr 1
  have : (1 - a) ≠ 0 := by linarith
  unfold latK2 latPhi
  field_simp
  ring

lemma latPhi_mono (hβ1 : β ≤ 1) {a b : ℝ} (h : a ≤ b) : latPhi β a ≤ latPhi β b := by
  unfold latPhi; nlinarith

lemma latPhi_range (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) :
    -1 ≤ latPhi β a ∧ latPhi β a ≤ 1 := by
  unfold latPhi; constructor <;> nlinarith

/-- Case 1 of the reduction: on the feasible set `D ≥ 0`, the certificate gives
`φ(a)φ(b) + k(a)k(b)(s - ab) ≤ S`. -/
lemma lat_core (hcert : LatSign s c S β) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc1 : c < 1)
    {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ c) (hb : -1 ≤ b) (hb' : b ≤ c)
    (hD : 0 ≤ 1 - s ^ 2 + 2 * s * (a * b) - a ^ 2 - b ^ 2) :
    latPhi β a * latPhi β b + latK β a * latK β b * (s - a * b) ≤ S := by
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  set L := latK β a * latK β b with hL
  have hL0 : 0 ≤ L := mul_nonneg (latK_nonneg _ _) (latK_nonneg _ _)
  have hU : 0 < (1 - a) * (1 - b) := mul_pos (by linarith) (by linarith)
  have hL2 : L ^ 2 = latK2 β a * latK2 β b := by
    rw [hL, mul_pow, latK, latK, Real.sq_sqrt (latK2_nonneg hβ0 hβ1.le ha ha1),
      Real.sq_sqrt (latK2_nonneg hβ0 hβ1.le hb hb1)]
  have hH : latH s S β a b =
      (1 - a) * (1 - b) * (latP S β a b ^ 2 - L ^ 2 * (s - a * b) ^ 2) := by
    rw [hL2]
    have h1 : (1 - a) ≠ 0 := by linarith
    have h2 : (1 - b) ≠ 0 := by linarith
    unfold latH latK2
    field_simp
  have key : L * (s - a * b) ≤ latP S β a b := by
    rcases hcert a b ha ha' hb hb' hD with ⟨hP, hV⟩ | ⟨hP, hH0⟩ | ⟨hV, hH0⟩
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hL0 hV]
    · rw [hH] at hH0
      have hsq : (L * (s - a * b)) ^ 2 ≤ latP S β a b ^ 2 := by
        have := (mul_nonneg_iff_of_pos_left hU).mp hH0
        nlinarith
      nlinarith [sq_nonneg (L * (s - a * b) - latP S β a b)]
    · rw [hH] at hH0
      have hsq : latP S β a b ^ 2 ≤ (L * (s - a * b)) ^ 2 := by
        have : (latP S β a b ^ 2 - L ^ 2 * (s - a * b) ^ 2) ≤ 0 := by
          by_contra h
          push Not at h
          nlinarith [mul_pos hU h]
        nlinarith
      have hLV : L * (s - a * b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hL0 hV
      nlinarith [sq_nonneg (L * (s - a * b) - latP S β a b)]
  unfold latP at key
  linarith

/-- Case 2 of the reduction (the meridian argument): if `a ≤ b` and the largest inner product
`ab + √(1-a²)√(1-b²)` of two unit vectors at latitudes `a, b` is below `s`, then the transformed
inner product at that position is still at most `S`. -/
lemma lat_meridian (hcert : LatSign s c S β) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc1 : c < 1)
    (hs1 : -1 ≤ s) (hs2 : s ≤ 1)
    {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb' : b ≤ c)
    (hlt : a * b + √(1 - a ^ 2) * √(1 - b ^ 2) < s) :
    latPhi β a * latPhi β b + latK β a * latK β b * (√(1 - a ^ 2) * √(1 - b ^ 2)) ≤ S := by
  have hb : -1 ≤ b := ha.trans hab
  have ha' : a ≤ c := hab.trans hb'
  have hca : cos (arccos a) = a := cos_arccos ha (by linarith)
  have hcb : cos (arccos b) = b := cos_arccos hb (by linarith)
  have hθ : arccos b ≤ arccos a := arccos_le_arccos hab
  have hcos : cos (arccos a - arccos b) < cos (arccos s) := by
    rw [cos_sub, hca, hcb, sin_arccos, sin_arccos, cos_arccos hs1 hs2]; exact hlt
  have hgt : arccos s < arccos a - arccos b := by
    by_contra h
    push Not at h
    have := cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr hθ) (arccos_le_pi s) h
    linarith
  set θ := arccos b + arccos s with hθdef
  have hθ0 : 0 ≤ θ := add_nonneg (arccos_nonneg _) (arccos_nonneg _)
  have hθπ : θ ≤ π := by linarith [arccos_le_pi a]
  set a' := cos θ with ha'def
  have ha'1 : a ≤ a' := by
    rw [← hca]; exact cos_le_cos_of_nonneg_of_le_pi hθ0 (arccos_le_pi a) (by linarith)
  have ha'2 : a' ≤ b := by
    rw [← hcb]
    exact cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg b) hθπ (by linarith [arccos_nonneg s])
  have hsin' : sin θ = √(1 - a' ^ 2) := by rw [← sin_arccos, arccos_cos hθ0 hθπ]
  have hW : s - a' * b = √(1 - a' ^ 2) * √(1 - b ^ 2) := by
    have h := cos_sub θ (arccos b)
    rw [show θ - arccos b = arccos s by rw [hθdef]; ring, cos_arccos hs1 hs2, hcb, hsin',
      sin_arccos] at h
    rw [h]; ring
  have ha'r : -1 ≤ a' := ha.trans ha'1
  have ha'r' : a' ≤ 1 := by linarith
  have hD : 0 ≤ 1 - s ^ 2 + 2 * s * (a' * b) - a' ^ 2 - b ^ 2 := by
    have h1 : (s - a' * b) ^ 2 = (1 - a' ^ 2) * (1 - b ^ 2) := by
      rw [hW, mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
    nlinarith
  have hcore := lat_core hcert hβ0 hβ1 hc1 ha'r (ha'2.trans hb') hb hb' hD
  rw [hW, mul_mul_mul_comm, latK_mul_sqrt hβ0 hβ1.le ha'r (by linarith),
    latK_mul_sqrt hβ0 hβ1.le hb (by linarith)] at hcore
  rw [mul_mul_mul_comm, latK_mul_sqrt hβ0 hβ1.le ha (by linarith),
    latK_mul_sqrt hβ0 hβ1.le hb (by linarith)]
  -- both sides are cosines of differences of `ψ = arccos ∘ φ`
  obtain ⟨hpa, hpa'⟩ := latPhi_range hβ0 hβ1.le ha (by linarith)
  obtain ⟨hpb, hpb'⟩ := latPhi_range hβ0 hβ1.le hb (by linarith)
  obtain ⟨hpc, hpc'⟩ := latPhi_range hβ0 hβ1.le ha'r ha'r'
  have hcosψ : ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 →
      x * y + √(1 - x ^ 2) * √(1 - y ^ 2) = cos (arccos x - arccos y) := by
    intro x y hx hx' hy hy'
    rw [cos_sub, cos_arccos hx hx', cos_arccos hy hy', sin_arccos, sin_arccos]
  rw [hcosψ _ _ hpc hpc' hpb hpb'] at hcore
  rw [hcosψ _ _ hpa hpa' hpb hpb']
  have h1 : arccos (latPhi β b) ≤ arccos (latPhi β a') :=
    arccos_le_arccos (latPhi_mono hβ1.le ha'2)
  have h2 : arccos (latPhi β a') ≤ arccos (latPhi β a) :=
    arccos_le_arccos (latPhi_mono hβ1.le ha'1)
  have := cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr h1)
    (by linarith [arccos_le_pi (latPhi β a), arccos_nonneg (latPhi β b)])
    (by linarith : arccos (latPhi β a') - arccos (latPhi β b) ≤
      arccos (latPhi β a) - arccos (latPhi β b))
  linarith

/-- The latitude comparison: for unit vectors at latitudes `a, b ∈ [-1, c]` with inner product
`t ≤ s`, the transformed inner product `φ(a)φ(b) + k(a)k(b)(t - ab)` is at most `S`. The
hypothesis `|t - ab| ≤ √(1-a²)√(1-b²)` is Cauchy–Schwarz for the parts orthogonal to the
pole. -/
theorem lat_key (hcert : LatSign s c S β) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc1 : c < 1)
    (hs1 : -1 ≤ s) (hs2 : s ≤ 1)
    {a b t : ℝ} (ha : -1 ≤ a) (ha' : a ≤ c) (hb : -1 ≤ b) (hb' : b ≤ c) (ht : t ≤ s)
    (hreal : |t - a * b| ≤ √(1 - a ^ 2) * √(1 - b ^ 2)) :
    latPhi β a * latPhi β b + latK β a * latK β b * (t - a * b) ≤ S := by
  set W := √(1 - a ^ 2) * √(1 - b ^ 2) with hWdef
  have hL0 : 0 ≤ latK β a * latK β b := mul_nonneg (latK_nonneg _ _) (latK_nonneg _ _)
  have hW2 : W ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) := by
    rw [hWdef, mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
  have hW0 : 0 ≤ W := by positivity
  rcases le_or_gt 0 (1 - s ^ 2 + 2 * s * (a * b) - a ^ 2 - b ^ 2) with hD | hD
  · have := lat_core hcert hβ0 hβ1 hc1 ha ha' hb hb' hD
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : t - a * b ≤ s - a * b) hL0]
  · -- `(s - ab)² > W²`
    have hsq : W ^ 2 < (s - a * b) ^ 2 := by nlinarith
    have habs := abs_le.mp hreal
    rcases lt_or_ge (s - a * b) 0 with hneg | hpos
    · -- then `s - ab < -W ≤ t - ab ≤ s - ab`, impossible
      nlinarith
    · have hWs : W < s - a * b := by nlinarith
      have hstep : latPhi β a * latPhi β b + latK β a * latK β b * W ≤ S := by
        rcases le_total a b with hab | hab
        · exact lat_meridian hcert hβ0 hβ1 hc1 hs1 hs2 ha hab hb' (by linarith)
        · have := lat_meridian hcert hβ0 hβ1 hc1 hs1 hs2 hb hab ha'
            (by rw [mul_comm b a, mul_comm (√(1 - b ^ 2))]; linarith)
          rw [mul_comm (latPhi β b), mul_comm (latK β b), mul_comm (√(1 - b ^ 2))] at this
          exact this
      nlinarith [mul_le_mul_of_nonneg_left habs.2 hL0]

end scalar

/-! ## Affine latitude: the map on the sphere -/

section map

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The affine latitude map about the pole `p`:
`T(u) = φ(a) p + k(a) (u - a p)` with `a = ⟪u, p⟫`. -/
noncomputable def latMap (β : ℝ) (p u : V) : V :=
  latPhi β ⟪u, p⟫ • p + latK β ⟪u, p⟫ • (u - ⟪u, p⟫ • p)

variable {p : V} (hp : ‖p‖ = 1)
include hp

lemma inner_perp_perp (u v : V) :
    ⟪u - ⟪u, p⟫ • p, v - ⟪v, p⟫ • p⟫ = ⟪u, v⟫ - ⟪u, p⟫ * ⟪v, p⟫ := by
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hpp]
  rw [real_inner_comm p u, real_inner_comm p v]
  ring

lemma inner_latMap (β : ℝ) (u v : V) :
    ⟪latMap β p u, latMap β p v⟫ = latPhi β ⟪u, p⟫ * latPhi β ⟪v, p⟫ +
      latK β ⟪u, p⟫ * latK β ⟪v, p⟫ * (⟪u, v⟫ - ⟪u, p⟫ * ⟪v, p⟫) := by
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  have h1 : ∀ w : V, ⟪p, w - ⟪w, p⟫ • p⟫ = 0 := fun w => by
    rw [inner_sub_right, real_inner_smul_right, hpp, real_inner_comm]; ring
  have h2 : ∀ w : V, ⟪w - ⟪w, p⟫ • p, p⟫ = 0 := fun w => by rw [real_inner_comm, h1]
  simp only [latMap, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hpp, h1, h2, inner_perp_perp hp]
  ring

lemma inner_latMap_pole (β : ℝ) (u : V) : ⟪latMap β p u, p⟫ = latPhi β ⟪u, p⟫ := by
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  have h2 : ⟪u - ⟪u, p⟫ • p, p⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hpp]; ring
  simp only [latMap, inner_add_left, real_inner_smul_left, hpp, h2]
  ring

lemma norm_latMap {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {u : V} (hu : ‖u‖ = 1)
    (ha : -1 ≤ ⟪u, p⟫) (ha1 : ⟪u, p⟫ < 1) : ‖latMap β p u‖ = 1 := by
  have h := inner_latMap hp β u u
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  rw [huu, real_inner_self_eq_norm_sq] at h
  set a := ⟪u, p⟫
  have hk : latK β a * latK β a = latK2 β a :=
    Real.mul_self_sqrt (latK2_nonneg hβ0 hβ1 ha ha1)
  have hk2 : latK2 β a * (1 - a * a) = 1 - latPhi β a ^ 2 := by
    have : (1 - a) ≠ 0 := by linarith
    unfold latK2 latPhi
    field_simp
    ring
  rw [hk, hk2] at h
  have : ‖latMap β p u‖ ^ 2 = 1 := by rw [h]; ring
  have h0 := norm_nonneg (latMap β p u)
  nlinarith

/-- Cauchy–Schwarz for the parts orthogonal to the pole. -/
lemma abs_inner_sub_le {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |⟪u, v⟫ - ⟪u, p⟫ * ⟪v, p⟫| ≤ √(1 - ⟪u, p⟫ ^ 2) * √(1 - ⟪v, p⟫ ^ 2) := by
  have hn : ∀ w : V, ‖w‖ = 1 → ‖w - ⟪w, p⟫ • p‖ = √(1 - ⟪w, p⟫ ^ 2) := by
    intro w hw
    have h := inner_perp_perp hp w w
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw] at h
    rw [← Real.sqrt_sq (norm_nonneg (w - ⟪w, p⟫ • p)), h]
    congr 1; ring
  rw [← inner_perp_perp hp, ← hn u hu, ← hn v hv]
  exact abs_real_inner_le_norm _ _

end map

/-! ## The latitude implication -/

/-- `s = 1 - 1/(2r²)`, the inner cutoff. -/
noncomputable def latS (r : ℝ) : ℝ := 1 - 1 / (2 * r ^ 2)

/-- `c = (r² + R² - 1)/(2rR)`, the pole cutoff. -/
noncomputable def latC (r R : ℝ) : ℝ := (r ^ 2 + R ^ 2 - 1) / (2 * r * R)

/-- `β = max(0, (c - S)/(1 + c))` with `S = 203/400`. -/
noncomputable def latBeta (r R : ℝ) : ℝ := max 0 ((latC r R - 203 / 400) / (1 + latC r R))

/-- The statement that `affine_latitude_counts.py` `check(r, R)` certifies for the inner radius
`r` and outer radius `R`, with spherical cutoff `S = 203/400`. -/
def LatitudeCert (r R : ℝ) : Prop := LatSign (latS r) (latC r R) (203 / 400) (latBeta r R)

lemma latC_pos {r R : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R) : 0 < latC r R := by
  unfold latC; apply div_pos <;> nlinarith

lemma latC_lt_one {r R : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R) (hR2 : R ^ 2 ≤ 2) : latC r R < 1 := by
  unfold latC
  rw [div_lt_one (by nlinarith)]
  have : R < 2 := by nlinarith
  nlinarith

lemma latBeta_nonneg (r R : ℝ) : 0 ≤ latBeta r R := le_max_left _ _

lemma latBeta_lt_one {r R : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R) : latBeta r R < 1 := by
  have hc := latC_pos hr hrR
  unfold latBeta
  apply max_lt (by norm_num)
  rw [div_lt_one (by linarith)]
  linarith

lemma latPhi_latC_le {r R : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    latPhi (latBeta r R) (latC r R) ≤ 203 / 400 := by
  have hc := latC_pos hr hrR
  have hβ : (latC r R - 203 / 400) / (1 + latC r R) ≤ latBeta r R := le_max_right _ _
  rw [div_le_iff₀ (by linarith)] at hβ
  unfold latPhi
  nlinarith


lemma latS_range {r : ℝ} (hr : 1 ≤ r) : -1 ≤ latS r ∧ latS r ≤ 1 := by
  unfold latS
  have : 0 < 2 * r ^ 2 := by positivity
  have h1 : 1 / (2 * r ^ 2) ≤ 1 := by rw [div_le_one this]; nlinarith
  constructor
  · linarith
  · linarith [div_pos one_pos this]

/-- **Affine latitude implication.** If an admissible neighbourhood has 24 points within the
inner radius `r`, it has no further point within the outer radius `R`. The proof maps the 24
inner directions by the affine latitude map about the direction of the outer point; with that
direction they form a 25-point code with cosine at most `203/400`. -/
theorem latitude_count {r R : ℝ} (hcode : SphericalCodeBound (203 / 400) 24)
    (hcert : LatitudeCert r R) (hr : 1 ≤ r) (hrR : r ≤ R) (hR2 : R ^ 2 ≤ 2)
    {X : Finset E4} (hX : Admissible X) (h24 : countWithin X r = 24) :
    countWithin X R = 24 := by
  classical
  have hr2 : r ^ 2 ≤ 2 := le_trans (by nlinarith) hR2
  set A := X.filter fun x => ‖x‖ ≤ r with hA
  have hAc : A.card = 24 := h24
  -- every point within `R` is within `r`
  suffices hall : ∀ y ∈ X, ‖y‖ ≤ R → ‖y‖ ≤ r by
    have : (X.filter fun x => ‖x‖ ≤ R) = A := by
      ext x; simp only [hA, Finset.mem_filter]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, hall x hx h⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, h.trans hrR⟩
    unfold countWithin; rw [this]; exact hAc
  intro y hy hyR
  by_contra hyr
  push Not at hyr
  have hy1 : 1 ≤ ‖y‖ := hX.1 y hy
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hy1; norm_num at hy1
  set p := dir y with hpdef
  have hp : ‖p‖ = 1 := norm_dir hy0
  set β := latBeta r R
  set c := latC r R
  set s := latS r
  have hβ0 : 0 ≤ β := latBeta_nonneg r R
  have hβ1 : β < 1 := latBeta_lt_one hr hrR
  have hc1 : c < 1 := latC_lt_one hr hrR hR2
  obtain ⟨hs1, hs2⟩ := latS_range hr
  have hmemA : ∀ x ∈ A, x ∈ X ∧ ‖x‖ ≤ r := fun x hx => Finset.mem_filter.mp hx
  have hx0 : ∀ x ∈ A, x ≠ 0 := fun x hx h => by
    have := hX.1 x (hmemA x hx).1; rw [h, norm_zero] at this; norm_num at this
  have hunit : ∀ x ∈ A, ‖dir x‖ = 1 := fun x hx => norm_dir (hx0 x hx)
  -- latitudes of inner directions lie in `[-1, c]`
  have hlat : ∀ x ∈ A, -1 ≤ ⟪dir x, p⟫ ∧ ⟪dir x, p⟫ ≤ c := by
    intro x hx
    constructor
    · have := neg_le_of_abs_le (abs_real_inner_le_norm (dir x) p)
      rwa [hunit x hx, hp, mul_one] at this
    · have hxy : x ≠ y := fun h => by have := (hmemA x hx).2; rw [h] at this; linarith
      exact inner_dir_le (hx0 x hx) hy0 (two_shell_inner_le (hX.1 x (hmemA x hx).1)
        (hmemA x hx).2 hy1 hyR hr2 hR2 (hX.2 x (hmemA x hx).1 y hy hxy))
  -- inner pairs have inner product at most `s`
  have hpair : ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ⟪dir x, dir x'⟫ ≤ s := by
    intro x hx x' hx' hne
    exact inner_dir_le (hx0 x hx) (hx0 x' hx') (shell_inner_le (hX.1 x (hmemA x hx).1)
      (hmemA x hx).2 (hX.1 x' (hmemA x' hx').1) (hmemA x' hx').2 hr2
      (hX.2 x (hmemA x hx).1 x' (hmemA x' hx').1 hne))
  set T : E4 → E4 := fun x => latMap β p (dir x) with hT
  have hTunit : ∀ x ∈ A, ‖T x‖ = 1 := fun x hx =>
    norm_latMap hp hβ0 hβ1.le (hunit x hx) (hlat x hx).1 ((hlat x hx).2.trans_lt hc1)
  have hTpole : ∀ x ∈ A, ⟪T x, p⟫ ≤ 203 / 400 := by
    intro x hx
    rw [hT, inner_latMap_pole hp]
    exact (latPhi_mono hβ1.le (hlat x hx).2).trans (latPhi_latC_le hr hrR)
  have hTpair : ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → ⟪T x, T x'⟫ ≤ 203 / 400 := by
    intro x hx x' hx' hne
    rw [hT, inner_latMap hp]
    exact lat_key hcert hβ0 hβ1 hc1 hs1 hs2 (hlat x hx).1 (hlat x hx).2 (hlat x' hx').1
      (hlat x' hx').2 (hpair x hx x' hx' hne) (abs_inner_sub_le hp (hunit x hx) (hunit x' hx'))
  have hTinj : Set.InjOn T (A : Set E4) := by
    intro x hx x' hx' h
    by_contra hne
    have := hTpair x hx x' hx' hne
    rw [h, real_inner_self_eq_norm_sq, hTunit x' hx'] at this
    norm_num at this
  have hpnot : p ∉ A.image T := by
    intro hmem
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hmem
    have := hTpole x hx
    rw [hxp, real_inner_self_eq_norm_sq, hp] at this
    norm_num at this
  -- the 25-point code
  have hcard : (insert p (A.image T)).card = 25 := by
    rw [Finset.card_insert_of_notMem hpnot, Finset.card_image_of_injOn hTinj, hAc]
  have := hcode (insert p (A.image T)) (by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hp
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu; exact hTunit x hx)
    (by
      intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with rfl | hu <;> rcases Finset.mem_insert.mp hv with rfl | hv
      · exact absurd rfl huv
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
        rw [real_inner_comm]; exact hTpole x hx
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        exact hTpole x hx
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hv
        exact hTpair x hx x' hx' fun h => huv (by rw [h]))
  omega

/-! ## Caps and monotonicity -/

lemma countWithin_mono (X : Finset E4) {r r' : ℝ} (h : r ≤ r') :
    countWithin X r ≤ countWithin X r' := by
  unfold countWithin
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

/-- A cap from a spherical code bound: if `1 - 1/(2R²) ≤ ρ < 1` and `A(4, ρ) ≤ m`, an admissible
neighbourhood has at most `m` points within `R`. -/
theorem countWithin_le_of_code {R ρ : ℝ} {m : ℕ} (hcode : SphericalCodeBound ρ m)
    (hρ : 1 - 1 / (2 * R ^ 2) ≤ ρ) (hρ1 : ρ < 1) (hR2 : R ^ 2 ≤ 2)
    {X : Finset E4} (hX : Admissible X) : countWithin X R ≤ m := by
  unfold countWithin
  apply card_le_of_cos_le hcode hρ1
  · intro x hx h0
    have := hX.1 x (Finset.mem_filter.mp hx).1
    rw [h0, norm_zero] at this; norm_num at this
  · intro x hx y hy hne
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have h := shell_inner_le (hX.1 x hx'.1) hx'.2 (hX.1 y hy'.1) hy'.2 hR2
      (hX.2 x hx'.1 y hy'.1 hne)
    have hxy : 0 ≤ ‖x‖ * ‖y‖ := by positivity
    nlinarith

/-! ## The count domain -/

/-- The count domain `C` of the census (paper, Lemma 4.1; stage 2 README item 1). -/
def CountDomain (n₁ n₂ n₃ n₄ n₅ : ℕ) : Prop :=
  n₁ ≤ n₂ ∧ n₂ ≤ n₃ ∧ n₃ ≤ n₄ ∧ n₄ ≤ n₅ ∧
    n₁ ≤ 24 ∧ n₂ ≤ 24 ∧ n₃ ≤ 24 ∧ n₄ ≤ 25 ∧ n₅ ≤ 26 ∧
    0 ≤ (23 - (n₁ : ℤ)) * ((n₅ : ℤ) - n₁) ∧ 0 ≤ (23 - (n₂ : ℤ)) * ((n₄ : ℤ) - n₂)

/-- The count vector of `X` lies in the count domain. -/
def InCountDomain (X : Finset E4) : Prop :=
  CountDomain (countWithin X R1) (countWithin X R2) (countWithin X R3) (countWithin X R4)
    (countWithin X R5)

/-- The hypotheses behind the count domain: three spherical code bounds and two affine
latitude certificates. -/
structure CountHyps : Prop where
  code24 : SphericalCodeBound (203 / 400) 24
  code25 : SphericalCodeBound (103 / 200) 25
  code26 : SphericalCodeBound (21 / 40) 26
  lat15 : LatitudeCert R1 R5
  lat24 : LatitudeCert R2 R4

lemma conditional_ray {r R : ℝ} (hcode : SphericalCodeBound (203 / 400) 24)
    (hcert : LatitudeCert r R) (hr : 1 ≤ r) (hrR : r ≤ R) (hR2 : R ^ 2 ≤ 2)
    {X : Finset E4} (hX : Admissible X) (hcap : countWithin X r ≤ 24) :
    0 ≤ (23 - (countWithin X r : ℤ)) * ((countWithin X R : ℤ) - countWithin X r) := by
  have hmono := countWithin_mono X hrR
  rcases Nat.lt_or_ge (countWithin X r) 24 with h | h
  · apply mul_nonneg <;> omega
  · have h24 : countWithin X r = 24 := le_antisymm hcap h
    have := latitude_count hcode hcert hr hrR hR2 hX h24
    rw [h24, this]; norm_num

/-- **Lemma 4.1.** Every admissible neighbourhood has its count vector in the count domain. -/
theorem countDomain_of_admissible (h : CountHyps) {X : Finset E4} (hX : Admissible X) :
    InCountDomain X := by
  have m12 := countWithin_mono X (show R1 ≤ R2 by norm_num [R1, R2])
  have m23 := countWithin_mono X (show R2 ≤ R3 by norm_num [R2, R3])
  have m34 := countWithin_mono X (show R3 ≤ R4 by norm_num [R3, R4])
  have m45 := countWithin_mono X (show R4 ≤ R5 by norm_num [R4, R5])
  have c3 := countWithin_le_of_code (R := R3) h.code24 (by norm_num [R3]) (by norm_num)
    (by norm_num [R3]) hX
  have c4 := countWithin_le_of_code (R := R4) h.code25 (by norm_num [R4]) (by norm_num)
    (by norm_num [R4]) hX
  have c5 := countWithin_le_of_code (R := R5) h.code26 (by norm_num [R5]) (by norm_num)
    (by norm_num [R5]) hX
  have i15 := conditional_ray h.code24 h.lat15 (by norm_num [R1]) (by norm_num [R1, R5])
    (by norm_num [R5]) hX (by omega)
  have i24 := conditional_ray h.code24 h.lat24 (by norm_num [R2]) (by norm_num [R2, R4])
    (by norm_num [R4]) hX (by omega)
  exact ⟨m12, m23, m34, m45, by omega, by omega, c3, c4, c5, i15, i24⟩

/-! ## The group of a neighbourhood is in the ledger -/

/-- The keys `(N, j)` of the 124 groups. -/
def groupKeys : List (ℕ × ℕ) := groups.map fun g => (g.1, g.2.1)

/-- Each key occurs once. -/
theorem groupKeys_nodup : groupKeys.Nodup := by decide +kernel

/-- The ledger lists every group allowed by the caps: `(N, 1)` for `N ≤ 24`, `(N, 2)` and
`(N, 3)` for `1 ≤ N ≤ 24`, `(N, 4)` for `1 ≤ N ≤ 25` and `(N, 5)` for `1 ≤ N ≤ 26`. -/
theorem groupKeys_complete :
    (∀ N : ℕ, N < 25 → (N, 1) ∈ groupKeys) ∧ (∀ N : ℕ, N < 24 → (N + 1, 2) ∈ groupKeys) ∧
      (∀ N : ℕ, N < 24 → (N + 1, 3) ∈ groupKeys) ∧ (∀ N : ℕ, N < 25 → (N + 1, 4) ∈ groupKeys) ∧
      (∀ N : ℕ, N < 26 → (N + 1, 5) ∈ groupKeys) := by
  decide +kernel

/-- The group `(N, j)` of a neighbourhood in the count domain is one of the 124 groups. -/
theorem group_mem {X : Finset E4} (hD : InCountDomain X) :
    ∃ g ∈ groups, g.1 = nearCount X ∧ g.2.1 = firstRadius X := by
  obtain ⟨m12, m23, m34, m45, c1, c2, c3, c4, c5, -, -⟩ := hD
  obtain ⟨k1, k2, k3, k4, k5⟩ := groupKeys_complete
  have hkey : (nearCount X, firstRadius X) ∈ groupKeys := by
    unfold firstRadius nearCount
    split_ifs with h1 h2 h3 h4
    · exact k1 _ (by omega)
    · have := k2 (countWithin X R5 - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
    · have := k3 (countWithin X R5 - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
    · have := k4 (countWithin X R5 - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
    · have := k5 (countWithin X R5 - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
  obtain ⟨g, hg, hgk⟩ := List.mem_map.mp hkey
  exact ⟨g, hg, (Prod.mk.inj hgk).1, (Prod.mk.inj hgk).2⟩

end D4Bound
