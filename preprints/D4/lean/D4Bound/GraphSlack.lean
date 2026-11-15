import D4Bound.Neighbourhood
import D4Bound.Geometry

/-!
# The broad graph has at most 1208 ordered edges

`graphSlack_of`: every admissible neighbourhood has at most `151 · 8 = 1208` ordered edges of
the broad graph (vertices: radius in `[33/28, 7/4]`; edges: cosine at most `-7/8`). This is
Lemma 5.1 of the paper and `verify/stage4_graph_slack/proofs/graph_slack.md`. It rests on two
named hypotheses:

* `SphericalCodeBound (41/49) 151`: `A(4, 41/49) ≤ 151`, at most 151 unit vectors in `ℝ⁴` with pairwise inner
  products at most `41/49`. Stage 4 (`src/verify_annular_count_151.py`) checks the degree-20
  Delsarte polynomial that proves it; the passage from the polynomial to the count uses
  Schoenberg's theorem.
* `SchutteVanDerWaerden`: among any nine unit vectors in `ℝ³` two have inner product at least
  `1/3` (`φ₃(9) = arccos(1/3)`, Schütte and van der Waerden 1951). Cited, not proved.

Everything else is proved here: separated points of the annulus have cosine at most `41/49`
(`annulus_inner_le`), so there are at most 151 vertices; the neighbours of a vertex, projected
to the orthogonal complement of its direction and normalized, have pairwise inner products
below `1/3` (the bound `223/735` of the paper, here with the strict inequality that is
needed), so each vertex has degree at most 8.
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound

/-! ## The two hypotheses -/

/-- The nine-point theorem of Schütte and van der Waerden: any nine unit vectors in `ℝ³`
contain two (with distinct indices) whose inner product is at least `1/3`. -/
def SchutteVanDerWaerden : Prop :=
  ∀ x : Fin 9 → EuclideanSpace ℝ (Fin 3), (∀ i, ‖x i‖ = 1) →
    ∃ i j, i ≠ j ∧ 1 / 3 ≤ ⟪x i, x j⟫

/-! ## Nine points -/

/-- A finite set of unit vectors in `ℝ³` with pairwise inner products below `1/3` has at most
8 elements. -/
lemma card_le_eight_R3 (hS : SchutteVanDerWaerden) (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (hu : ∀ x ∈ S, ‖x‖ = 1) (hp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫ < 1 / 3) :
    S.card ≤ 8 := by
  by_contra h
  have h9 : 9 ≤ S.card := by omega
  let f : Fin 9 → EuclideanSpace ℝ (Fin 3) := fun i => (S.equivFin.symm (Fin.castLE h9 i)).1
  have hf : Function.Injective f := by
    intro i j hij
    have := Subtype.val_injective hij
    exact Fin.castLE_injective h9 (S.equivFin.symm.injective this)
  have hmem : ∀ i, f i ∈ S := fun i => (S.equivFin.symm (Fin.castLE h9 i)).2
  obtain ⟨i, j, hij, hle⟩ := hS f fun i => hu _ (hmem i)
  have := hp (f i) (hmem i) (f j) (hmem j) (hf.ne hij)
  linarith

/-- The same in the orthogonal complement of a nonzero vector of `ℝ⁴`. -/
lemma card_le_eight_perp (hS : SchutteVanDerWaerden) {w : E4} (hw : w ≠ 0) (S : Finset E4)
    (hperp : ∀ x ∈ S, ⟪w, x⟫ = 0) (hu : ∀ x ∈ S, ‖x‖ = 1)
    (hp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫ < 1 / 3) : S.card ≤ 8 := by
  classical
  have : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
  have hW : Module.finrank ℝ (ℝ ∙ w)ᗮ = 3 := Submodule.finrank_orthogonal_span_singleton hw
  let e : (ℝ ∙ w)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ((stdOrthonormalBasis ℝ (ℝ ∙ w)ᗮ).reindex (finCongr hW)).repr
  let g : E4 → EuclideanSpace ℝ (Fin 3) := fun x =>
    if hx : x ∈ (ℝ ∙ w)ᗮ then e ⟨x, hx⟩ else 0
  have hmemW : ∀ x ∈ S, x ∈ (ℝ ∙ w)ᗮ := fun x hx =>
    (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr (hperp x hx)
  have hg : ∀ x ∈ S, ∀ y ∈ S, ⟪g x, g y⟫ = ⟪x, y⟫ := by
    intro x hx y hy
    simp only [g, dif_pos (hmemW x hx), dif_pos (hmemW y hy), LinearIsometryEquiv.inner_map_map,
      Submodule.coe_inner]
  have hgn : ∀ x ∈ S, ‖g x‖ = 1 := by
    intro x hx
    have h := hg x hx x hx
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu x hx] at h
    have h0 : 0 ≤ ‖g x‖ := norm_nonneg _
    nlinarith
  have hinj : Set.InjOn g (S : Set E4) := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hg x hx y hy
    rw [← hxy, real_inner_self_eq_norm_sq, hgn x hx] at h1
    have := hp x hx y hy hne
    linarith
  rw [← Finset.card_image_of_injOn hinj]
  apply card_le_eight_R3 hS
  · intro u hu'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu'
    exact hgn x hx
  · intro u hu' v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    rw [hg x hx y hy]
    exact hp x hx y hy fun h => huv (by rw [h])

/-! ## The projected cosine -/

/-- For latitudes `a, b ∈ [7/8, 1]`: `41/49 - ab < √(1 - a²) √(1 - b²) / 3`. At
`a = b = 7/8` the left side is `(223/735)` times `√(1 - a²) √(1 - b²)`. -/
lemma proj_scalar {a b : ℝ} (ha : 7 / 8 ≤ a) (ha' : a ≤ 1) (hb : 7 / 8 ≤ b) (_hb' : b ≤ 1) :
    41 / 49 - a * b < Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) / 3 := by
  rw [← Real.sqrt_mul (by nlinarith)]
  rcases lt_or_ge (41 / 49 - a * b) 0 with h | h
  · have := Real.sqrt_nonneg ((1 - a ^ 2) * (1 - b ^ 2)); linarith
  · have hlt : 3 * (41 / 49 - a * b) < Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
      rw [Real.lt_sqrt (by linarith)]
      have hab : (49 / 64 : ℝ) ≤ a * b := by nlinarith
      have h1 : 0 ≤ (a ^ 2 - 49 / 64) * (b ^ 2 - 49 / 64) := by
        apply mul_nonneg <;> nlinarith
      have h2 : 0 ≤ (a * b - 49 / 64) * (41 / 49 - a * b) := mul_nonneg (by linarith) h
      nlinarith
    linarith

/-! ## Degree at most 8 -/

open Classical in
/-- In an admissible neighbourhood every point has at most 8 broad-graph neighbours. -/
theorem broad_degree_le (hS : SchutteVanDerWaerden) {X : Finset E4} (hX : Admissible X)
    (y : E4) : (X.filter fun z => broadEdge y z).card ≤ 8 := by
  classical
  set Z := X.filter fun z => broadEdge y z with hZ
  by_contra hcard
  have hZ2 : 2 ≤ Z.card := by omega
  have hmemZ : ∀ z ∈ Z, z ∈ X ∧ broadEdge y z := fun z hz => Finset.mem_filter.mp hz
  -- `y` is a vertex
  obtain ⟨z₀, hz₀⟩ : Z.Nonempty := Finset.card_pos.mp (by omega)
  have hy1 : 33 / 28 ≤ ‖y‖ := (hmemZ z₀ hz₀).2.1
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hy1; norm_num at hy1
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set w : E4 := -dir y with hw
  have hwn : ‖w‖ = 1 := by rw [hw, norm_neg, norm_dir hy0]
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hwn; norm_num at hwn
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hwn]; norm_num
  -- facts about one neighbour
  have hz0 : ∀ z ∈ Z, z ≠ 0 := fun z hz h => by
    have := (hmemZ z hz).2.2.2.1; rw [h, norm_zero] at this; norm_num at this
  set a : E4 → ℝ := fun z => ⟪dir z, w⟫ with ha
  have ha_ge : ∀ z ∈ Z, 7 / 8 ≤ a z := by
    intro z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (hz0 z hz)
    have he := (hmemZ z hz).2.2.2.2.2
    have : a z = -⟪y, z⟫ / (‖y‖ * ‖z‖) := by
      simp only [ha, hw, inner_neg_right, real_inner_comm, inner_dir]
      ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have ha_le : ∀ z ∈ Z, a z ≤ 1 := by
    intro z hz
    have := real_inner_le_norm (dir z) w
    rw [norm_dir (hz0 z hz), hwn] at this
    simpa [ha] using this
  have hdd : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ⟪dir z, dir z'⟫ ≤ 41 / 49 := by
    intro z hz z' hz' hne
    have e := (hmemZ z hz).2
    have e' := (hmemZ z' hz').2
    exact inner_dir_le (hz0 z hz) (hz0 z' hz')
      (annulus_inner_le e.2.2.1 e.2.2.2.1 e'.2.2.1 e'.2.2.2.1
        (hX.2 z (hmemZ z hz).1 z' (hmemZ z' hz').1 hne))
  -- the projection `p z = dir z - a z • w`
  set p : E4 → E4 := fun z => dir z - a z • w with hp
  have hp_inner : ∀ z z', ⟪p z, p z'⟫ = ⟪dir z, dir z'⟫ - a z * a z' := by
    intro z z'
    simp only [hp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hww, ha]
    rw [real_inner_comm w (dir z')]
    ring
  have hp_norm : ∀ z ∈ Z, ‖p z‖ = Real.sqrt (1 - a z ^ 2) := by
    intro z hz
    have h := hp_inner z z
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_dir (hz0 z hz)] at h
    rw [← Real.sqrt_sq (norm_nonneg (p z))]
    congr 1
    linarith
  have hp_perp : ∀ z, ⟪w, p z⟫ = 0 := by
    intro z
    simp only [hp, inner_sub_right, real_inner_smul_right, hww, ha]
    rw [real_inner_comm]; ring
  have hp_lt : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ⟪p z, p z'⟫ < ‖p z‖ * ‖p z'‖ / 3 := by
    intro z hz z' hz' hne
    rw [hp_inner, hp_norm z hz, hp_norm z' hz']
    have := proj_scalar (ha_ge z hz) (ha_le z hz) (ha_ge z' hz') (ha_le z' hz')
    linarith [hdd z hz z' hz' hne]
  have hp0 : ∀ z ∈ Z, p z ≠ 0 := by
    intro z hz h0
    obtain ⟨z', hz', hne⟩ : ∃ z' ∈ Z, z' ≠ z := by
      by_contra hall
      push Not at hall
      have : Z ⊆ {z} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
      have := Finset.card_le_card this
      simp at this; omega
    have := hp_lt z hz z' hz' (Ne.symm hne)
    rw [h0, inner_zero_left, norm_zero, zero_mul, zero_div] at this
    exact lt_irrefl _ this
  -- normalized projections
  set x : E4 → E4 := fun z => dir (p z) with hx
  have hx_lt : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ⟪x z, x z'⟫ < 1 / 3 := by
    intro z hz z' hz' hne
    have h1 := norm_pos_iff.mpr (hp0 z hz)
    have h2 := norm_pos_iff.mpr (hp0 z' hz')
    simp only [hx]
    rw [inner_dir, div_lt_iff₀ (by positivity)]
    linarith [hp_lt z hz z' hz' hne]
  have hx_unit : ∀ z ∈ Z, ‖x z‖ = 1 := fun z hz => norm_dir (hp0 z hz)
  have hx_inj : Set.InjOn x (Z : Set E4) := by
    intro z hz z' hz' h
    by_contra hne
    have := hx_lt z hz z' hz' hne
    rw [h, real_inner_self_eq_norm_sq, hx_unit z' hz'] at this
    norm_num at this
  have hle : (Z.image x).card ≤ 8 := by
    apply card_le_eight_perp hS hw0
    · intro u hu
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hu
      simp only [hx, dir, real_inner_smul_right, hp_perp, mul_zero]
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
      exact hx_unit z hz
    · intro u hu v hv huv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hv
      exact hx_lt z hz z' hz' fun h => huv (by rw [h])
  rw [Finset.card_image_of_injOn hx_inj] at hle
  exact hcard hle

/-! ## The edge count -/

open Classical in
lemma broadEdges_eq_sum (X : Finset E4) :
    broadEdges X = ∑ y ∈ X, (X.filter fun z => broadEdge y z).card := by
  classical
  rw [broadEdges, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.card_filter]

/-- At most 151 vertices: the vertices of an admissible neighbourhood. -/
theorem broad_vertices_le (hA : SphericalCodeBound (41 / 49) 151) {X : Finset E4} (hX : Admissible X) :
    (X.filter fun y => 33 / 28 ≤ ‖y‖ ∧ ‖y‖ ≤ 7 / 4).card ≤ 151 := by
  classical
  apply card_le_of_cos_le hA (by norm_num)
  · intro x hx h0
    have := (Finset.mem_filter.mp hx).2.1
    rw [h0, norm_zero] at this; norm_num at this
  · intro x hx y hy hne
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact annulus_inner_le hx'.2.1 hx'.2.2 hy'.2.1 hy'.2.2 (hX.2 x hx'.1 y hy'.1 hne)

/-- **Lemma 5.1.** Every admissible neighbourhood has at most 1208 ordered broad-graph edges. -/
theorem broadEdges_le (hA : SphericalCodeBound (41 / 49) 151) (hS : SchutteVanDerWaerden) {X : Finset E4}
    (hX : Admissible X) : broadEdges X ≤ 1208 := by
  classical
  set V := X.filter fun y => 33 / 28 ≤ ‖y‖ ∧ ‖y‖ ≤ 7 / 4
  have hzero : ∀ y ∈ X, y ∉ V → (X.filter fun z => broadEdge y z).card = 0 := by
    intro y hy hyV
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z _ he
    exact hyV (Finset.mem_filter.mpr ⟨hy, he.1, he.2.1⟩)
  have hsplit : ∑ y ∈ X, (X.filter fun z => broadEdge y z).card =
      ∑ y ∈ V, (X.filter fun z => broadEdge y z).card := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y hy => ?_
    split_ifs with h
    · rfl
    · exact hzero y hy fun hV => h (Finset.mem_filter.mp hV).2
  rw [broadEdges_eq_sum, hsplit]
  calc ∑ y ∈ V, (X.filter fun z => broadEdge y z).card ≤ ∑ _y ∈ V, 8 :=
        Finset.sum_le_sum fun y _ => broad_degree_le hS hX y
    _ = 8 * V.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 8 * 151 := Nat.mul_le_mul_left 8 (broad_vertices_le hA hX)
    _ = 1208 := by norm_num

end D4Bound
