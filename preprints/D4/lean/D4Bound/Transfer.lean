import D4Bound.Density
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod

/-!
# From the finite-patch inequality to the density of a packing

Let `f : ℝ⁴ → ℝ` be continuous and integrable, with integrable Fourier transform `f̂` whose real
part is `≥ 0`, `∫ f = I > 0`, and `f ≤ 0` outside a ball of radius `R0`. If every finite
unit-separated family satisfies `∑_{i,j} f (p j - p i) ≤ n C`, then every unit packing has upper
density at most `(π² / 32) C / I` (`D4Bound.transfer`).

The proof uses no periodization and no Poisson summation. Let `X` be the centres in `B(0,R)`,
`N = #X`, `W = B(0, ρ)` with `ρ = R + max R0 0`, `μ` the sum of Dirac masses on `X` and `ν`
Lebesgue measure on `W`. Put `q(α, β) = ∫∫ f (y - x) dβ(y) dα(x)`.

1. Positive definiteness (`TransferAux.pd_real`): for finite measures and real `t`,
   `q(μ,μ) - t q(μ,ν) - t q(ν,μ) + t² q(ν,ν) = ∫ Re f̂ · |μ̂ - t ν̂|² ≥ 0`.
   This is Fourier inversion (`Continuous.fourierInv_fourier_eq`) and one Fubini swap.
2. `q(μ,μ) = ∑_{i,j} f (p j - p i) ≤ N C`, and `q(μ,ν), q(ν,μ) ≥ N I` because `f ≤ 0`
   outside `B(0, R0)` and `B(p, R0) ⊆ W` for `p ∈ X`.
3. `q(ν,ν) ≤ vol(W) (I + e)`, where `e` is the tail mass of `|f|` beyond `√R` plus
   `∫|f|` times the relative volume of the shell of width `√R` (`TransferAux.double_upper`).
4. With `t = N / vol(W)`: `N² (I - e) ≤ N C vol(W)`. As `R → ∞`, `e → 0` and
   `vol(W) / vol(B(0,R)) → 1`, which gives the bound on the `limsup`.

`D4Bound.transfer_quarter` is the case `I = π² / 4`, with bound `C / 8`.
-/

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace ComplexConjugate ENNReal

namespace D4Bound.TransferAux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Fourier transform of a finite measure. -/
noncomputable def ch (μ : Measure V) (ξ : V) : ℂ := ∫ x, (𝐞 (-⟪x, ξ⟫) : ℂ) ∂μ

/-- The pair form `∫∫ g (y - x) dν(y) dμ(x)`. -/
noncomputable def Q (g : V → ℂ) (μ ν : Measure V) : ℂ := ∫ x, ∫ y, g (y - x) ∂ν ∂μ

variable {g : V → ℂ}

lemma continuous_fourier_of_integrable (hi : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi

lemma inv_formula (hc : Continuous g) (hi : Integrable g) (hF : Integrable (𝓕 g)) (z : V) :
    g z = ∫ ξ, (𝐞 ⟪ξ, z⟫ : ℂ) * 𝓕 g ξ := by
  have := congrFun (hc.fourierInv_fourier_eq hi hF) z
  rw [Real.fourierInv_eq] at this
  rw [← this]
  simp [Circle.smul_def]

lemma norm_le_of_inv (hc : Continuous g) (hi : Integrable g) (hF : Integrable (𝓕 g)) (z : V) :
    ‖g z‖ ≤ ∫ ξ, ‖𝓕 g ξ‖ := by
  rw [inv_formula hc hi hF z]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext ξ
  simp [Circle.norm_coe]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma kernel_eq (x y ξ : V) :
    (𝐞 ⟪ξ, y - x⟫ : ℂ) = (𝐞 (-⟪x, ξ⟫) : ℂ) * conj (𝐞 (-⟪y, ξ⟫) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right, real_inner_comm x, real_inner_comm y]
  ring_nf

lemma integrable_kernel (hi : Integrable g) (hF : Integrable (𝓕 g))
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (Function.uncurry fun (z : V × V) (ξ : V) => (𝐞 ⟪ξ, z.2 - z.1⟫ : ℂ) * 𝓕 g ξ)
      ((μ.prod ν).prod volume) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hF.norm) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have h1 : Continuous fun w : (V × V) × V => (𝐞 ⟪w.2, w.1.2 - w.1.1⟫ : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_inner.comp (continuous_snd.prodMk
          ((continuous_snd.comp continuous_fst).sub (continuous_fst.comp continuous_fst)))))
    exact h1.mul ((continuous_fourier_of_integrable hi).comp continuous_snd)
  · refine Filter.Eventually.of_forall fun w => ?_
    simp [Function.uncurry, Circle.norm_coe]

lemma integrable_pair (hc : Continuous g) (hi : Integrable g) (hF : Integrable (𝓕 g))
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z : V × V => g (z.2 - z.1)) (μ.prod ν) :=
  Integrable.of_bound ((hc.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable) _
    (Filter.Eventually.of_forall fun _ => norm_le_of_inv hc hi hF _)

lemma Q_eq (hc : Continuous g) (hi : Integrable g) (hF : Integrable (𝓕 g))
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Q g μ ν = ∫ ξ, 𝓕 g ξ * (ch μ ξ * conj (ch ν ξ)) ∧
      Integrable (fun ξ => 𝓕 g ξ * (ch μ ξ * conj (ch ν ξ))) := by
  have hK := integrable_kernel hi hF μ ν
  have hpt : ∀ ξ, ∫ z, (𝐞 ⟪ξ, z.2 - z.1⟫ : ℂ) * 𝓕 g ξ ∂(μ.prod ν) =
      𝓕 g ξ * (ch μ ξ * conj (ch ν ξ)) := by
    intro ξ
    simp_rw [kernel_eq, mul_comm _ (𝓕 g ξ)]
    rw [integral_const_mul, integral_prod_mul (fun x => (𝐞 (-⟪x, ξ⟫) : ℂ))
      (fun y => conj (𝐞 (-⟪y, ξ⟫) : ℂ)), integral_conj]
    rfl
  constructor
  · unfold Q
    rw [← integral_prod _ (integrable_pair hc hi hF μ ν)]
    simp_rw [inv_formula hc hi hF (_ - _)]
    rw [integral_integral_swap hK]
    simp_rw [hpt]
  · have h2 := hK.swap.integral_prod_left
    simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, Function.uncurry] at h2
    simpa only [hpt] using h2

lemma pd (hc : Continuous g) (hi : Integrable g) (hF : Integrable (𝓕 g))
    (hre : ∀ ξ, 0 ≤ (𝓕 g ξ).re)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    0 ≤ (Q g μ μ - t * Q g μ ν - t * Q g ν μ + t ^ 2 * Q g ν ν).re := by
  obtain ⟨e1, i1⟩ := Q_eq hc hi hF μ μ
  obtain ⟨e2, i2⟩ := Q_eq hc hi hF μ ν
  obtain ⟨e3, i3⟩ := Q_eq hc hi hF ν μ
  obtain ⟨e4, i4⟩ := Q_eq hc hi hF ν ν
  set F1 := fun ξ => 𝓕 g ξ * (ch μ ξ * conj (ch μ ξ))
  set F2 := fun ξ => 𝓕 g ξ * (ch μ ξ * conj (ch ν ξ))
  set F3 := fun ξ => 𝓕 g ξ * (ch ν ξ * conj (ch μ ξ))
  set F4 := fun ξ => 𝓕 g ξ * (ch ν ξ * conj (ch ν ξ))
  have j2 : Integrable (fun ξ => (t : ℂ) * F2 ξ) := i2.const_mul _
  have j3 : Integrable (fun ξ => (t : ℂ) * F3 ξ) := i3.const_mul _
  have j4 : Integrable (fun ξ => (t : ℂ) ^ 2 * F4 ξ) := i4.const_mul _
  have j12 : Integrable (fun ξ => F1 ξ - (t : ℂ) * F2 ξ) := i1.sub j2
  have j123 : Integrable (fun ξ => F1 ξ - (t : ℂ) * F2 ξ - (t : ℂ) * F3 ξ) := j12.sub j3
  have j : Integrable (fun ξ => F1 ξ - (t : ℂ) * F2 ξ - (t : ℂ) * F3 ξ + (t : ℂ) ^ 2 * F4 ξ) :=
    j123.add j4
  have hsum : ∫ ξ, (F1 ξ - (t : ℂ) * F2 ξ - (t : ℂ) * F3 ξ + (t : ℂ) ^ 2 * F4 ξ) =
      (∫ ξ, F1 ξ) - t * (∫ ξ, F2 ξ) - t * (∫ ξ, F3 ξ) + (t : ℂ) ^ 2 * (∫ ξ, F4 ξ) := by
    rw [integral_add j123 j4, integral_sub j12 j3, integral_sub i1 j2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e1, e2, e3, e4, ← hsum]
  refine le_of_le_of_eq (integral_nonneg fun ξ => ?_) (integral_re j)
  show 0 ≤ (F1 ξ - (t : ℂ) * F2 ξ - (t : ℂ) * F3 ξ + (t : ℂ) ^ 2 * F4 ξ).re
  set A := ch μ ξ
  set B := ch ν ξ
  have : 𝓕 g ξ * (A * conj A) - (t : ℂ) * (𝓕 g ξ * (A * conj B)) -
      (t : ℂ) * (𝓕 g ξ * (B * conj A)) + (t : ℂ) ^ 2 * (𝓕 g ξ * (B * conj B)) =
      𝓕 g ξ * ((A - t * B) * conj (A - t * B)) := by
    simp only [map_sub, map_mul, conj_ofReal]
    ring
  simp only [F1, F2, F3, F4]
  rw [this, mul_conj, mul_comm, re_ofReal_mul]
  exact mul_nonneg (normSq_nonneg _) (hre ξ)


/-! ### Real-valued kernels -/

section Real

variable {f : V → ℝ}

/-- The real pair form `∫∫ f (y - x) dν(y) dμ(x)`. -/
noncomputable def q (f : V → ℝ) (μ ν : Measure V) : ℝ := ∫ x, ∫ y, f (y - x) ∂ν ∂μ

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
lemma Q_ofReal (μ ν : Measure V) : Q (fun x => (f x : ℂ)) μ ν = (q f μ ν : ℂ) := by
  unfold Q q
  simp_rw [integral_complex_ofReal]

lemma pd_real (hc : Continuous f) (hi : Integrable f) (hF : Integrable (𝓕 (fun x => (f x : ℂ))))
    (hre : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    0 ≤ q f μ μ - t * q f μ ν - t * q f ν μ + t ^ 2 * q f ν ν := by
  have h := pd (g := fun x => (f x : ℂ)) (continuous_ofReal.comp hc) hi.ofReal hF hre μ ν t
  simp only [Q_ofReal] at h
  have e : ((q f μ μ : ℂ) - t * q f μ ν - t * q f ν μ + (t : ℂ) ^ 2 * q f ν ν) =
      ((q f μ μ - t * q f μ ν - t * q f ν μ + t ^ 2 * q f ν ν : ℝ) : ℂ) := by push_cast; ring
  rwa [e, ofReal_re] at h

lemma abs_le_of_inv (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ)))) (z : V) :
    |f z| ≤ ∫ ξ, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ := by
  have := norm_le_of_inv (g := fun x => (f x : ℂ)) (continuous_ofReal.comp hc) hi.ofReal hF z
  simpa using this

lemma integrable_pair_real (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ))))
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z : V × V => f (z.2 - z.1)) (μ.prod ν) :=
  Integrable.of_bound ((hc.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable) _
    (Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs]; exact abs_le_of_inv hc hi hF _)

/-- Sum of Dirac masses at the points of a finite family. -/
noncomputable def diracSum {n : ℕ} (p : Fin n → V) : Measure V := ∑ i, Measure.dirac (p i)

instance {n : ℕ} (p : Fin n → V) : IsFiniteMeasure (diracSum p) := by
  constructor
  simp [diracSum, Measure.finsetSum_apply]

lemma integral_diracSum {n : ℕ} (p : Fin n → V) (h : V → ℝ) :
    ∫ x, h x ∂(diracSum p) = ∑ i, h (p i) := by
  unfold diracSum
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac]

end Real


/-! ### Window estimates -/

section Bounds

open Metric

variable {f : V → ℝ}

/-- Tail mass `∫_{‖z‖ ≥ s} |f z|`. -/
noncomputable def tail (f : V → ℝ) (s : ℝ) : ℝ :=
  ∫ z, Set.indicator {z : V | s ≤ ‖z‖} (fun z => |f z|) z

lemma tail_nonneg (s : ℝ) : 0 ≤ tail f s :=
  integral_nonneg fun _ => Set.indicator_nonneg (fun _ _ => abs_nonneg _) _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma measurableSet_tail (s : ℝ) : MeasurableSet {z : V | s ≤ ‖z‖} :=
  (isClosed_le continuous_const continuous_norm).measurableSet

lemma setIntegral_ge_of_nonpos_off {h : V → ℝ} (hh : Integrable h) {W : Set V}
    (hW : MeasurableSet W) (hoff : ∀ y ∉ W, h y ≤ 0) : ∫ y, h y ≤ ∫ y in W, h y := by
  rw [← integral_add_compl hW hh]
  have : ∫ y in Wᶜ, h y ≤ 0 := setIntegral_nonpos hW.compl (fun y hy => hoff y hy)
  linarith

lemma inner_lower_right {R0 : ℝ} (hi : Integrable f) (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    {W : Set V} (hW : MeasurableSet W) (p : V) (hp : ∀ y, ‖y - p‖ < R0 → y ∈ W) :
    ∫ z, f z ≤ ∫ y in W, f (y - p) := by
  rw [← integral_sub_right_eq_self f p]
  exact setIntegral_ge_of_nonpos_off (hi.comp_sub_right p) hW
    (fun y hy => hneg _ (not_lt.1 fun h => hy (hp y h)))

lemma inner_lower_left {R0 : ℝ} (hi : Integrable f) (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    {W : Set V} (hW : MeasurableSet W) (p : V) (hp : ∀ y, ‖y - p‖ < R0 → y ∈ W) :
    ∫ z, f z ≤ ∫ x in W, f (p - x) := by
  rw [← integral_sub_left_eq_self f volume p]
  exact setIntegral_ge_of_nonpos_off (hi.comp_sub_left p) hW
    (fun y hy => hneg _ (by rw [norm_sub_rev]; exact not_lt.1 fun h => hy (hp y h)))

lemma inner_upper (hi : Integrable f) {W : Set V} (hW : MeasurableSet W) (x : V) :
    ∫ y in W, f (y - x) ≤ (∫ z, f z) + ∫ y in Wᶜ, |f (y - x)| := by
  have h1 : (∫ y in W, f (y - x)) + (∫ y in Wᶜ, f (y - x)) = ∫ z, f z := by
    rw [integral_add_compl hW (hi.comp_sub_right x)]
    exact integral_sub_right_eq_self f x
  have h2 : -(∫ y in Wᶜ, f (y - x)) ≤ ∫ y in Wᶜ, |f (y - x)| := by
    rw [← integral_neg]
    exact integral_mono (hi.comp_sub_right x).integrableOn.neg
      (hi.comp_sub_right x).abs.integrableOn (fun y => neg_le_abs _)
  linarith

lemma compl_le_L (hi : Integrable f) (W : Set V) (x : V) :
    ∫ y in Wᶜ, |f (y - x)| ≤ ∫ z, |f z| := by
  refine (setIntegral_le_integral (hi.comp_sub_right x).abs
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)).trans (le_of_eq ?_)
  exact integral_sub_right_eq_self (fun z => |f z|) x

lemma compl_le_tail (hi : Integrable f) {W : Set V} (hW : MeasurableSet W) (x : V) (s : ℝ)
    (hfar : ∀ y ∉ W, s ≤ ‖y - x‖) : ∫ y in Wᶜ, |f (y - x)| ≤ tail f s := by
  rw [← integral_indicator hW.compl]
  have hT : Integrable (fun y => Set.indicator {z : V | s ≤ ‖z‖} (fun z => |f z|) (y - x)) :=
    (hi.abs.indicator (measurableSet_tail s)).comp_sub_right x
  refine (integral_mono ((hi.comp_sub_right x).abs.indicator hW.compl) hT ?_).trans (le_of_eq ?_)
  · intro y
    by_cases hy : y ∈ W
    · rw [Set.indicator_of_notMem (by simpa using hy)]
      exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
    · rw [Set.indicator_of_mem (by simpa using hy)]
      dsimp only
      rw [Set.indicator_of_mem (show y - x ∈ {z : V | s ≤ ‖z‖} from hfar y hy)]
  · exact integral_sub_right_eq_self
      (fun z => Set.indicator {z : V | s ≤ ‖z‖} (fun z => |f z|) z) x

lemma double_upper (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ)))) (ρ s : ℝ) (hs : 0 ≤ s) :
    q f (volume.restrict (ball (0 : V) ρ)) (volume.restrict (ball (0 : V) ρ)) ≤
      ((∫ z, f z) + tail f s) * volume.real (ball (0 : V) ρ) +
        (∫ z, |f z|) * (volume.real (ball (0 : V) ρ) - volume.real (ball (0 : V) (ρ - s))) := by
  set W := ball (0 : V) ρ with hWdef
  set B' := ball (0 : V) (ρ - s) with hB'def
  have : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hBW : B' ⊆ W := ball_subset_ball (by linarith)
  have hmeas : MeasurableSet (W \ B') := measurableSet_ball.diff measurableSet_ball
  set L := ∫ z, |f z|
  have hL : 0 ≤ L := integral_nonneg fun _ => abs_nonneg _
  set φ : V → ℝ := fun x => ((∫ z, f z) + tail f s) + (W \ B').indicator (fun _ => L) x
  have hint : IntegrableOn (fun x => ∫ y in W, f (y - x)) W :=
    (integrable_pair_real hc hi hF (volume.restrict W) (volume.restrict W)).integral_prod_left
  have hφ : IntegrableOn φ W :=
    (integrable_const _).add ((integrable_const _).indicator hmeas)
  have hle : ∀ x ∈ W, ∫ y in W, f (y - x) ≤ φ x := by
    intro x _
    have hu : ∫ y in W, f (y - x) ≤ (∫ z, f z) + ∫ y in Wᶜ, |f (y - x)| :=
      inner_upper hi measurableSet_ball x
    by_cases hxB : x ∈ B'
    · have hfar : ∀ y ∉ W, s ≤ ‖y - x‖ := by
        intro y hy
        have h1 : ρ ≤ ‖y‖ := by simpa [hWdef, mem_ball_zero_iff] using hy
        have h2 : ‖x‖ < ρ - s := by simpa [hB'def, mem_ball_zero_iff] using hxB
        have h3 := norm_sub_norm_le y x
        linarith
      have : ∫ y in Wᶜ, |f (y - x)| ≤ tail f s := compl_le_tail hi measurableSet_ball x s hfar
      have h0 : 0 ≤ (W \ B').indicator (fun _ => L) x := Set.indicator_nonneg (fun _ _ => hL) _
      simp only [φ]
      linarith
    · have : ∫ y in Wᶜ, |f (y - x)| ≤ L := compl_le_L hi W x
      have hxm : x ∈ W \ B' := ⟨by assumption, hxB⟩
      simp only [φ, Set.indicator_of_mem hxm]
      have : 0 ≤ tail f s := tail_nonneg s
      linarith
  calc ∫ x in W, ∫ y in W, f (y - x) ≤ ∫ x in W, φ x := setIntegral_mono_on hint hφ measurableSet_ball hle
    _ = ((∫ z, f z) + tail f s) * volume.real W + L * (volume.real W - volume.real B') := by
      simp only [φ]
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hmeas),
        setIntegral_const, setIntegral_indicator hmeas, setIntegral_const,
        Set.inter_eq_right.2 Set.sdiff_subset, measureReal_sdiff hBW measurableSet_ball, smul_eq_mul,
        smul_eq_mul]
      ring

/-- The finite-window inequality: for a separated family whose `R0`-neighbourhoods lie in the
ball of radius `ρ`, `n² (V (I - T) - L (V - V')) ≤ n C V²`. -/
theorem finite_bound {R0 : ℝ} (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ)))) (hre : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0) (C : ℝ)
    (hpatch : ∀ (n : ℕ) (p : Fin n → V), (∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖) →
      ∑ i, ∑ j, f (p j - p i) ≤ n * C)
    {n : ℕ} (p : Fin n → V) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖)
    (ρ s : ℝ) (hs : 0 ≤ s) (hV : 0 < volume.real (ball (0 : V) ρ))
    (hp : ∀ i y, ‖y - p i‖ < R0 → ‖y‖ < ρ) :
    (n : ℝ) ^ 2 * (volume.real (ball (0 : V) ρ) * ((∫ z, f z) - tail f s) -
      (∫ z, |f z|) * (volume.real (ball (0 : V) ρ) - volume.real (ball (0 : V) (ρ - s)))) ≤
      n * C * volume.real (ball (0 : V) ρ) ^ 2 := by
  set W := ball (0 : V) ρ with hWdef
  set Vρ := volume.real W
  set Vs := volume.real (ball (0 : V) (ρ - s))
  set I := ∫ z, f z
  set T := tail f s
  set L := ∫ z, |f z|
  set ν := volume.restrict W
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set μ := diracSum p
  set t : ℝ := n / Vρ with htdef
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hV.le
  have hmemW : ∀ i y, ‖y - p i‖ < R0 → y ∈ W := fun i y hy => mem_ball_zero_iff.2 (hp i y hy)
  have h := pd_real hc hi hF hre μ ν t
  have e1 : q f μ μ = ∑ i, ∑ j, f (p j - p i) := by simp only [q, μ, integral_diracSum]
  have e2 : q f μ ν = ∑ i, ∫ y in W, f (y - p i) := by simp only [q, μ, integral_diracSum]; rfl
  have e3 : q f ν μ = ∑ j, ∫ x in W, f (p j - x) := by
    simp only [q, μ, integral_diracSum]
    exact integral_finsetSum _ fun j _ => (hi.comp_sub_left (p j)).integrableOn
  have hS : q f μ μ ≤ n * C := e1 ▸ hpatch n p hsep
  have hA : n * I ≤ q f μ ν := by
    rw [e2]
    calc (n : ℝ) * I = ∑ _i : Fin n, I := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        inner_lower_right hi hneg measurableSet_ball (p i) (hmemW i)
  have hA' : n * I ≤ q f ν μ := by
    rw [e3]
    calc (n : ℝ) * I = ∑ _i : Fin n, I := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        inner_lower_left hi hneg measurableSet_ball (p i) (hmemW i)
  have hB : q f ν ν ≤ (I + T) * Vρ + L * (Vρ - Vs) := double_upper hc hi hF ρ s hs
  have m1 : t * (n * I) ≤ t * q f μ ν := mul_le_mul_of_nonneg_left hA ht0
  have m2 : t * (n * I) ≤ t * q f ν μ := mul_le_mul_of_nonneg_left hA' ht0
  have m3 : t ^ 2 * q f ν ν ≤ t ^ 2 * ((I + T) * Vρ + L * (Vρ - Vs)) :=
    mul_le_mul_of_nonneg_left hB (sq_nonneg t)
  have h1 : 0 ≤ n * C - 2 * t * (n * I) + t ^ 2 * ((I + T) * Vρ + L * (Vρ - Vs)) := by linarith
  have h2 := mul_nonneg (sq_nonneg Vρ) h1
  have e : Vρ ^ 2 * (n * C - 2 * t * (n * I) + t ^ 2 * ((I + T) * Vρ + L * (Vρ - Vs))) =
      n * C * Vρ ^ 2 - (n : ℝ) ^ 2 * (Vρ * (I - T) - L * (Vρ - Vs)) := by
    rw [htdef]
    field_simp
    ring
  rw [e] at h2
  linarith

end Bounds


/-! ### Tail decay -/

lemma tail_tendsto {f : V → ℝ} (hi : Integrable f) :
    Filter.Tendsto (tail f) Filter.atTop (nhds 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun s z => Set.indicator {z : V | s ≤ ‖z‖} (fun z => |f z|) z) (f := fun _ => (0 : ℝ))
    (l := Filter.atTop) (fun z => |f z|)
    (Filter.Eventually.of_forall fun s =>
      (hi.abs.indicator (measurableSet_tail s)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)]
      exact Set.indicator_le_self' (fun _ _ => abs_nonneg _) z)
    hi.abs
    (Filter.Eventually.of_forall fun z => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop ‖z‖] with s hs
      rw [Set.indicator_of_notMem (by simpa using hs)])
  simp only [integral_zero] at h
  exact h


open Metric Filter

section Main

open D4Bound

variable {f : E4 → ℝ} {C R0 : ℝ}

/-- Error term at radius `R`: window radius `R + max R0 0`, shell width `√R`. -/
noncomputable def err (f : E4 → ℝ) (R0 R : ℝ) : ℝ :=
  tail f √R + (∫ z, |f z|) * (1 - ((R + max R0 0 - √R) / (R + max R0 0)) ^ 4)

/-- The density bound at radius `R`. -/
noncomputable def bnd (f : E4 → ℝ) (C R0 R : ℝ) : ℝ :=
  Real.pi ^ 2 / 32 * C / ((∫ z, f z) - err f R0 R) * (1 + max R0 0 / R) ^ 4

lemma card_sq_bound (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ)))) (hre : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    (hpatch : ∀ (n : ℕ) (p : Fin n → E4), (∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖) →
      ∑ i, ∑ j, f (p j - p i) ≤ n * C)
    {P : Set E4} (hP : IsUnitPacking P) {R : ℝ} (hR : 1 ≤ R)
    (X : Finset E4) (hX : (X : Set E4) ⊆ P ∩ ball 0 R) :
    (X.card : ℝ) ^ 2 * ((∫ z, f z) - err f R0 R) ≤
      X.card * (C * (Real.pi ^ 2 / 2) * (R + max R0 0) ^ 4) := by
  have hm := le_max_right R0 0
  have hm' := le_max_left R0 0
  have hρpos : 0 < R + max R0 0 := by linarith
  have hs0 : 0 ≤ √R := Real.sqrt_nonneg _
  have hsR : √R ≤ R := Real.sqrt_le_self_iff.2 (Or.inr hR)
  have hsρ : 0 ≤ R + max R0 0 - √R := by linarith
  let p : Fin X.card → E4 := fun i => (X.equivFin.symm i : E4)
  have hpX : ∀ i, p i ∈ X := fun i => (X.equivFin.symm i).2
  have hsep : ∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖ := by
    intro i j hij
    have hne : p j ≠ p i := fun h => hij (X.equivFin.symm.injective (Subtype.ext h))
    rw [← dist_eq_norm]
    exact hP _ (hX (hpX j)).1 _ (hX (hpX i)).1 hne
  have hp : ∀ i y, ‖y - p i‖ < R0 → ‖y‖ < R + max R0 0 := by
    intro i y hy
    have h1 : ‖p i‖ < R := mem_ball_zero_iff.1 (hX (hpX i)).2
    have h2 := norm_sub_norm_le y (p i)
    linarith
  have hV : 0 < volume.real (ball (0 : E4) (R + max R0 0)) := by
    rw [volume_real_ball_E4 _ hρpos.le]; positivity
  have h := finite_bound hc hi hF hre hneg C hpatch p hsep (R + max R0 0) √R hs0 hV hp
  rw [volume_real_ball_E4 _ hρpos.le, volume_real_ball_E4 _ hsρ] at h
  have hc4 : 0 < Real.pi ^ 2 / 2 * (R + max R0 0) ^ 4 := by positivity
  have key : (Real.pi ^ 2 / 2 * (R + max R0 0) ^ 4) *
      ((X.card : ℝ) ^ 2 * ((∫ z, f z) - err f R0 R)) =
      (X.card : ℝ) ^ 2 * (Real.pi ^ 2 / 2 * (R + max R0 0) ^ 4 * ((∫ z, f z) - tail f √R) -
        (∫ z, |f z|) * (Real.pi ^ 2 / 2 * (R + max R0 0) ^ 4 -
          Real.pi ^ 2 / 2 * (R + max R0 0 - √R) ^ 4)) := by
    simp only [err]
    field_simp
    ring
  have key2 : (X.card : ℝ) * C * (Real.pi ^ 2 / 2 * (R + max R0 0) ^ 4) ^ 2 =
      (Real.pi ^ 2 / 2 * (R + max R0 0) ^ 4) *
        (X.card * (C * (Real.pi ^ 2 / 2) * (R + max R0 0) ^ 4)) := by ring
  rw [← key, key2] at h
  exact le_of_mul_le_mul_left h hc4

lemma err_tendsto (hi : Integrable f) : Tendsto (err f R0) atTop (nhds 0) := by
  have hm := le_max_right R0 0
  have hT : Tendsto (fun R => tail f √R) atTop (nhds 0) :=
    (tail_tendsto hi).comp Real.tendsto_sqrt_atTop
  have hinv : Tendsto (fun R : ℝ => 1 / √R) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hq : Tendsto (fun R => √R / (R + max R0 0)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with R hR
      exact div_nonneg (Real.sqrt_nonneg _) (by linarith)
    · filter_upwards [eventually_gt_atTop 0] with R hR
      rw [← Real.sqrt_div_self']
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hR (by linarith)
  have hr : Tendsto (fun R => (R + max R0 0 - √R) / (R + max R0 0)) atTop (nhds (1 - 0)) := by
    refine (tendsto_const_nhds.sub hq).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have : R + max R0 0 ≠ 0 := by linarith
    field_simp
  have h := hT.add (tendsto_const_nhds (x := ∫ z, |f z|) |>.mul
    (tendsto_const_nhds (x := (1 : ℝ)) |>.sub (hr.pow 4)))
  simp only [sub_zero, one_pow, sub_self, mul_zero, add_zero] at h
  exact h

lemma bnd_tendsto (hi : Integrable f) (hI : 0 < ∫ z, f z) :
    Tendsto (bnd f C R0) atTop (nhds (Real.pi ^ 2 / 32 * C / ∫ z, f z)) := by
  have h1 : Tendsto (fun R => (∫ z, f z) - err f R0 R) atTop (nhds ((∫ z, f z) - 0)) :=
    tendsto_const_nhds.sub (err_tendsto hi)
  have h2 : Tendsto (fun R : ℝ => (1 + max R0 0 / R) ^ 4) atTop (nhds ((1 + 0) ^ 4)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).pow 4
  have h := (tendsto_const_nhds (x := Real.pi ^ 2 / 32 * C)).div h1 (by simpa using hI.ne')
    |>.mul h2
  simp only [sub_zero, add_zero, one_pow, mul_one] at h
  exact h

lemma finite_inter_ball (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ)))) (hre : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    (hpatch : ∀ (n : ℕ) (p : Fin n → E4), (∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖) →
      ∑ i, ∑ j, f (p j - p i) ≤ n * C)
    (hIpos : 0 < ∫ z, f z) {P : Set E4} (hP : IsUnitPacking P) (R : ℝ) :
    (P ∩ ball 0 R).Finite := by
  obtain ⟨R1, hR1⟩ := eventually_atTop.1 ((err_tendsto (R0 := R0) hi).eventually (gt_mem_nhds hIpos))
  set R' := max (max R 1) R1
  have he : err f R0 R' < ∫ z, f z := hR1 R' (le_max_right _ _)
  have hR'1 : 1 ≤ R' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRR' : R ≤ R' := le_trans (le_max_left _ _) (le_max_left _ _)
  by_contra hinf
  set K := C * (Real.pi ^ 2 / 2) * (R' + max R0 0) ^ 4
  set e := err f R0 R'
  obtain ⟨X, hXs, hXc⟩ := Set.Infinite.exists_subset_card_eq hinf
    (⌈K / ((∫ z, f z) - e)⌉₊ + 1)
  have hX' : (X : Set E4) ⊆ P ∩ ball 0 R' :=
    hXs.trans (Set.inter_subset_inter_right _ (ball_subset_ball hRR'))
  have h := card_sq_bound hc hi hF hre hneg hpatch hP hR'1 X hX'
  rw [hXc] at h
  set m : ℝ := ((⌈K / ((∫ z, f z) - e)⌉₊ + 1 : ℕ) : ℝ) with hmdef
  have hm : 0 < m := by positivity
  have hpos : 0 < (∫ z, f z) - e := sub_pos.2 he
  have h1 : m * (m * ((∫ z, f z) - e)) ≤ m * K := by
    calc m * (m * ((∫ z, f z) - e)) = m ^ 2 * ((∫ z, f z) - e) := by ring
      _ ≤ m * K := h
  have h2 : m * ((∫ z, f z) - e) ≤ K := le_of_mul_le_mul_left h1 hm
  have h3 : m ≤ K / ((∫ z, f z) - e) := (le_div_iff₀ hpos).2 h2
  have h4 : K / ((∫ z, f z) - e) < m := by
    rw [hmdef]
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  linarith


lemma density_eventually_le (hc : Continuous f) (hi : Integrable f)
    (hF : Integrable (𝓕 (fun x => (f x : ℂ)))) (hre : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    (hpatch : ∀ (n : ℕ) (p : Fin n → E4), (∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖) →
      ∑ i, ∑ j, f (p j - p i) ≤ n * C)
    (hIpos : 0 < ∫ z, f z) {P : Set E4} (hP : IsUnitPacking P) :
    ∀ᶠ R in atTop, volume (ball (0 : E4) (1 / 2)) * ((P ∩ ball (0 : E4) R).encard : ENNReal) /
      volume (ball (0 : E4) R) ≤ ENNReal.ofReal (bnd f C R0 R) := by
  obtain ⟨R1, hR1⟩ := eventually_atTop.1 ((err_tendsto (R0 := R0) hi).eventually (gt_mem_nhds hIpos))
  filter_upwards [eventually_ge_atTop (max R1 1)] with R hR
  have hR1' : 1 ≤ R := le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := by linarith
  have he : err f R0 R < ∫ z, f z := hR1 R (le_trans (le_max_left _ _) hR)
  have hpos : 0 < (∫ z, f z) - err f R0 R := sub_pos.2 he
  have hfin := finite_inter_ball hc hi hF hre hneg hpatch hIpos hP R
  set X := hfin.toFinset
  have hX : (X : Set E4) ⊆ P ∩ ball 0 R := by simp [X]
  have henc : (P ∩ ball (0 : E4) R).encard = X.card := hfin.encard_eq_coe_toFinset_card
  rw [henc, show ((X.card : ℕ∞) : ENNReal) = ((X.card : ℕ) : ENNReal) from by simp]
  rcases Nat.eq_zero_or_pos X.card with h0 | hcard
  · simp [h0]
  have h := card_sq_bound hc hi hF hre hneg hpatch hP hR1' X hX
  set N : ℝ := (X.card : ℝ)
  set K := C * (Real.pi ^ 2 / 2) * (R + max R0 0) ^ 4
  have hN : 0 < N := by simp [N, hcard]
  have h2 : N * ((∫ z, f z) - err f R0 R) ≤ K := by
    have h1 : N * (N * ((∫ z, f z) - err f R0 R)) ≤ N * K := by
      calc N * (N * ((∫ z, f z) - err f R0 R)) = N ^ 2 * ((∫ z, f z) - err f R0 R) := by ring
        _ ≤ N * K := h
    exact le_of_mul_le_mul_left h1 hN
  have h3 : N ≤ K / ((∫ z, f z) - err f R0 R) := (le_div_iff₀ hpos).2 h2
  rw [volume_ball_E4, volume_ball_E4]
  apply ENNReal.div_le_of_le_mul
  have hc0 : (0 : ℝ) ≤ Real.pi ^ 2 / 2 := by positivity
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow hRpos.le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul' (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have eq : bnd f C R0 R * (R ^ 4 * (Real.pi ^ 2 / 2)) =
      (1 / 2) ^ 4 * (Real.pi ^ 2 / 2) * (K / ((∫ z, f z) - err f R0 R)) := by
    simp only [bnd, K]
    field_simp
    ring
  rw [eq]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end Main

end D4Bound.TransferAux

namespace D4Bound

open MeasureTheory Metric Filter D4Bound.TransferAux

/-- **Density transfer.** If `f` is continuous and integrable on `ℝ⁴`, its Fourier transform is
integrable with nonnegative real part, `∫ f = I > 0`, `f ≤ 0` outside the ball of radius `R0`,
and every finite unit-separated family satisfies `∑_{i,j} f (p j - p i) ≤ n C`, then every unit
packing has upper density at most `(π² / 32) C / I`. -/
theorem transfer (f : E4 → ℝ) (C I R0 : ℝ)
    (hcont : Continuous f) (hint : Integrable f)
    (hFint : Integrable (𝓕 (fun x => (f x : ℂ))))
    (hFnonneg : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (hI : ∫ x, f x = I) (hIpos : 0 < I)
    (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    (hpatch : ∀ (n : ℕ) (p : Fin n → E4), (∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖) →
      ∑ i, ∑ j, f (p j - p i) ≤ n * C)
    (P : Set E4) (hP : IsUnitPacking P) :
    upperDensity P ≤ ENNReal.ofReal (Real.pi ^ 2 / 32 * C / I) := by
  subst hI
  unfold upperDensity
  calc limsup (fun R : ℝ => volume (ball (0 : E4) (1 / 2)) *
        ((P ∩ ball (0 : E4) R).encard : ENNReal) / volume (ball (0 : E4) R)) atTop
      ≤ limsup (fun R => ENNReal.ofReal (bnd f C R0 R)) atTop :=
        limsup_le_limsup (density_eventually_le hcont hint hFint hFnonneg hneg hpatch hIpos hP)
    _ = ENNReal.ofReal (Real.pi ^ 2 / 32 * C / ∫ x, f x) :=
        (ENNReal.tendsto_ofReal (bnd_tendsto hint hIpos)).limsup_eq


/-- `transfer` with `I = π² / 4`: the bound is `C / 8`. -/
theorem transfer_quarter (f : E4 → ℝ) (C R0 : ℝ)
    (hcont : Continuous f) (hint : Integrable f)
    (hFint : Integrable (𝓕 (fun x => (f x : ℂ))))
    (hFnonneg : ∀ ξ, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (hI : ∫ x, f x = Real.pi ^ 2 / 4)
    (hneg : ∀ x, R0 ≤ ‖x‖ → f x ≤ 0)
    (hpatch : ∀ (n : ℕ) (p : Fin n → E4), (∀ i j, j ≠ i → 1 ≤ ‖p j - p i‖) →
      ∑ i, ∑ j, f (p j - p i) ≤ n * C)
    (P : Set E4) (hP : IsUnitPacking P) :
    upperDensity P ≤ ENNReal.ofReal (C / 8) := by
  have h := transfer f C (Real.pi ^ 2 / 4) R0 hcont hint hFint hFnonneg hI (by positivity)
    hneg hpatch P hP
  have e : Real.pi ^ 2 / 32 * C / (Real.pi ^ 2 / 4) = C / 8 := by
    field_simp
    ring
  rwa [e] at h

end D4Bound
