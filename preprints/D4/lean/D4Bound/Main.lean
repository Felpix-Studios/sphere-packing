import D4Bound.Allocation
import D4Bound.Ledger
import D4Bound.Scalar
import D4Bound.Transfer
import D4Bound.GraphSlack
import D4Bound.CountDomain
import D4Bound.AnnularCert
import D4Bound.LatitudeCert
import D4Bound.GraphSlackExact
import D4Bound.ProjectedEightCert

/-!
# The four-dimensional density bound

`d4_density_bound`: every unit packing `P ⊆ ℝ⁴` has upper density (`upperDensity`, defined in
`Density.lean`) below `0.629521681653`.

The scalar function `f` is concrete (`Scalar.lean`). This generic theorem takes a kernel `K`;
`V7Kernel.lean` defines the concrete kernel and `ConcreteMain.lean` specializes the result.
The generic theorem assumes the remaining facts that the programs in `../verify/` certify,
each as one named hypothesis:

| hypothesis       | statement                                                   | checker            |
|------------------|-------------------------------------------------------------|--------------------|
| `v7_support`     | `K(x,y) = 0` if `‖x‖ > 7/4` or `‖y‖ > 7/4` (`SupportedIn`)  | stage 1            |
| `v7_pair`        | `f(x) + 2K(x,0) + K(x,x) ≤ 0` for `‖x‖ ≥ 1` (`PairSign`)    | stage 1            |
| `v7_cyclic`      | `Γ(x,y) ≤ 0` on separated triangles (`CyclicSign`)          | stage 1            |
| `v7_raw`         | `f(0) + K(0,0) ≤ 8 urawUp` (`RawObjective`)                 | stage 1            |
| `census`         | `E_{K-Kg}(X) ≥` floor of the group of `X`, for `X` in the   | stages 2 and 3     |
|                  | count domain (`CensusFloor`)                                |                    |
| `kernel_box_1/5` | `-K ≥ λ_j q` on `B₁`, `B₅` (`KernelBox`)                    | stage 5            |
| `code_24/25/26`  | `A(4,203/400) ≤ 24`, `A(4,103/200) ≤ 25`, `A(4,21/40) ≤ 26` | stage 2            |
|                  | (`SphericalCodeBound`)                                      |                    |
| `latitude_15/24` | discharged by `LatitudeCheck.latitude15/24`               | Lean certificates  |
| `annular_151`    | discharged by `annular_151_proved` (`AnnularCert.lean`)    | Lean certificate   |
| `svdw`           | replaced by `projected_eight_proved` at cutoff `223/735`  | Lean certificate   |

Everything else is proved: the Fourier identity and signs of `f`, the allocation and its
triple-sum identity, the far-pair lemma, the graph slack (`GraphSlack.lean`), the count domain
and the group of every neighbourhood (`CountDomain.lean`), the
ledger over the 124 groups, the finite local-energy inequality and the density transfer.
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound

/-! ## The hypotheses -/

/-- Condition (2) of Theorem 2.1 for the base kernel. -/
def PairSign (K : E4 → E4 → ℝ) : Prop :=
  ∀ x : E4, 1 ≤ ‖x‖ → f x + 2 * K x 0 + K x x ≤ 0

/-- The raw objective: `(f(0) + K(0,0))/8 ≤ urawUp`. -/
def RawObjective (K : E4 → E4 → ℝ) : Prop :=
  f 0 + K 0 0 ≤ 8 * (urawUp : ℝ)

/-- The census: for an admissible neighbourhood whose count vector lies in the count domain,
the energy of `K` without the broad graph energy `Kg` is at least the floor of its group
`(N, j)`. That every admissible neighbourhood lies in the count domain, and that its group is
in the list, is proved (`countDomain_of_admissible`, `group_mem`). -/
def CensusFloor (K : E4 → E4 → ℝ) : Prop :=
  ∀ X : Finset E4, Admissible X → InCountDomain X →
    ∀ g ∈ groups, g.1 = nearCount X → g.2.1 = firstRadius X →
      (g.2.2 : ℝ) ≤ nbhdEnergy (fun x y => K x y - Kg x y) X

/-- The broad graph has at most 1208 ordered edges in every admissible neighbourhood. -/
def GraphSlack : Prop :=
  ∀ X : Finset E4, Admissible X → broadEdges X ≤ 1208

/-- Lemma 5.1: the graph slack follows from the annular count and the nine-point theorem. -/
theorem graphSlack_of (annular_151 : SphericalCodeBound (41 / 49) 151)
    (svdw : SchutteVanDerWaerden) : GraphSlack :=
  fun _ hX => broadEdges_le annular_151 svdw hX

/-- The graph slack with both finite-code inputs proved in Lean. The classical
nine-point theorem is no longer a premise of the density bound. -/
theorem graphSlack_proved : GraphSlack :=
  fun _ hX => broadEdges_le_projected annular_151_proved projected_eight_proved hX

/-! ## The energy floor of the allocated kernel -/

lemma all_le_R1 {X : Finset E4} (h : firstRadius X = 1) :
    ∀ x ∈ X, ‖x‖ ≤ R5 → ‖x‖ ≤ R1 := by
  classical
  have hc : countWithin X R1 = nearCount X := by
    by_contra hne
    simp only [firstRadius, if_neg hne] at h
    split_ifs at h <;> omega
  have hsub : (X.filter fun x => ‖x‖ ≤ R1) ⊆ X.filter fun x => ‖x‖ ≤ R5 :=
    fun x hx => by
      rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans R1_le_R5⟩
  have heq : (X.filter fun x => ‖x‖ ≤ R1) = X.filter fun x => ‖x‖ ≤ R5 :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [countWithin, nearCount] using hc.ge)
  intro x hx h5
  have : x ∈ X.filter fun x => ‖x‖ ≤ R1 := by rw [heq]; exact Finset.mem_filter.mpr ⟨hx, h5⟩
  exact (Finset.mem_filter.mp this).2

lemma nbhdEnergy_alloc (K : E4 → E4 → ℝ) (X : Finset E4) :
    nbhdEnergy (alloc K) X = ∑ x ∈ X, ∑ y ∈ X, alloc K x y := by
  simp [nbhdEnergy, alloc_zero_right]

/-- Every admissible neighbourhood has allocated energy at least `aLow + 3/10⁶`. -/
theorem energy_floor {K : E4 → E4 → ℝ} (v7_support : SupportedIn K)
    (v7_cyclic : CyclicSign K) (census : CensusFloor K) (graph_slack : GraphSlack)
    (count : CountHyps)
    (kernel_box_1 : KernelBox K R1 (3 / 1000000)) (kernel_box_5 : KernelBox K R5 (1 / 1000000))
    {X : Finset E4} (hX : Admissible X) :
    (aLow : ℝ) + 3 / 1000000 ≤ nbhdEnergy (Kalloc K) X := by
  have hD := countDomain_of_admissible count hX
  obtain ⟨g, hg, hN, hj⟩ := group_mem hD
  have hE := census X hX hD g hg hN hj
  have hG := nbhdEnergy_Kg_ge hX (graph_slack X hX)
  have hsplit : nbhdEnergy (Kalloc K) X =
      nbhdEnergy (fun x y => K x y - Kg x y) X + nbhdEnergy Kg X +
        ∑ x ∈ X, ∑ y ∈ X, alloc K x y := by
    rw [show Kalloc K = fun x y => K x y + alloc K x y from rfl, nbhdEnergy_add, nbhdEnergy_sub,
      nbhdEnergy_alloc]
    ring
  -- the far-pair gain
  have hfar : ((lam g.2.1 * max (QN g.1) 0 : ℚ) : ℝ) ≤ ∑ x ∈ X, ∑ y ∈ X, alloc K x y := by
    have hcast : ((lam g.2.1 * max (QN g.1) 0 : ℚ) : ℝ) = (lam g.2.1 : ℝ) *
        max ((nearCount X : ℝ) * (13561 * nearCount X - 179244) / 250000) 0 := by
      rw [Rat.cast_mul, Rat.cast_max, hN, QN]; push_cast; rfl
    rw [hcast]
    by_cases h1 : firstRadius X = 1
    · have : (lam g.2.1 : ℝ) = 3 / 1000000 := by rw [hj, h1, lam]; norm_num
      rw [this]
      exact far_pair_nbhd v7_support v7_cyclic hX (by norm_num) kernel_box_1 (all_le_R1 h1)
    · have : (lam g.2.1 : ℝ) = 1 / 1000000 := by rw [hj, lam, if_neg h1]; norm_num
      rw [this]
      exact far_pair_nbhd v7_support v7_cyclic hX (by norm_num) kernel_box_5
        (fun _ _ h => h)
  have hq : ((aLow : ℚ) : ℝ) ≤ ((g.2.2 + lam g.2.1 * max (QN g.1) 0 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (groups_ge g hg)
  rw [Rat.cast_add] at hq
  rw [hsplit]
  linarith

/-! ## The finite-patch inequality -/

/-- For every unit-separated finite family `p` in `ℝ⁴`,
`∑_{i,j} f(p_j - p_i) ≤ n (8 urawUp - aLow - 3/10⁶)`. -/
theorem d4_patch_bound {K : E4 → E4 → ℝ} (v7_support : SupportedIn K)
    (v7_pair : PairSign K) (v7_cyclic : CyclicSign K) (v7_raw : RawObjective K)
    (census : CensusFloor K) (graph_slack : GraphSlack) (count : CountHyps)
    (kernel_box_1 : KernelBox K R1 (3 / 1000000)) (kernel_box_5 : KernelBox K R5 (1 / 1000000))
    {n : ℕ} (p : Fin n → E4) (hp : Separated p) :
    ∑ i, ∑ j, f (p j - p i) ≤ n * (8 * (urawUp : ℝ) - aLow - 3 / 1000000) := by
  have hA : Kalloc K 0 0 = K 0 0 := Kalloc_diag K 0
  have hmain := finite_local_energy_of_tripleSum f (Kalloc K) (K 0 0) ((aLow : ℝ) + 3 / 1000000)
    p (fun i j hji => by
      rw [Kalloc_zero_right, Kalloc_diag]; exact v7_pair _ (hp i j hji))
    (tripleSum_Kalloc v7_support hp).le
    (fun i => by
      rw [← hA, energy_eq_nbhdEnergy hp]
      exact energy_floor v7_support v7_cyclic census graph_slack count kernel_box_1 kernel_box_5
        (nbhd_admissible hp i))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (n : ℝ) * (f 0 + K 0 0 - ((aLow : ℝ) + 3 / 1000000)) ≤
      n * (8 * (urawUp : ℝ) - aLow - 3 / 1000000) := by
    apply mul_le_mul_of_nonneg_left _ hn; unfold RawObjective at v7_raw; linarith
  linarith

/-! ## The bound -/

/-- **Theorem 1.1.** Every unit packing in `ℝ⁴` (centres at pairwise distance at least 1) has
upper density less than `0.629521681653`, given the remaining certified properties of `K`
and three spherical code bounds. The scalar function, latitude certificates, annular
count, and projected eight-point code bound are proved in Lean. -/
theorem d4_density_bound (K : E4 → E4 → ℝ)
    (v7_support : SupportedIn K)
    (v7_pair : PairSign K)
    (v7_cyclic : CyclicSign K)
    (v7_raw : RawObjective K)
    (census : CensusFloor K)
    (kernel_box_1 : KernelBox K R1 (3 / 1000000))
    (kernel_box_5 : KernelBox K R5 (1 / 1000000))
    (code_24 : SphericalCodeBound (203 / 400) 24)
    (code_25 : SphericalCodeBound (103 / 200) 25)
    (code_26 : SphericalCodeBound (21 / 40) 26)
    (P : Set E4) (hP : IsUnitPacking P) :
    upperDensity P < ENNReal.ofReal (629521681653 / 1000000000000) := by
  have graph_slack := graphSlack_proved
  have count : CountHyps := ⟨code_24, code_25, code_26, LatitudeCheck.latitude15, LatitudeCheck.latitude24⟩
  have fourier := fourierIdentity
  have h := transfer_quarter f (8 * (urawUp : ℝ) - aLow - 3 / 1000000) (7 / 4)
    f_continuous f_integrable (fourier_integrable fourier) (fourier_re_nonneg fourier)
    (integral_f fourier) (fun x hx => f_nonpos hx)
    (fun n p hp => d4_patch_bound v7_support v7_pair v7_cyclic v7_raw census graph_slack count
      kernel_box_1 kernel_box_5 p hp)
    P hP
  refine lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_)
  have hfin : ((urawUp - aLow / 8 - 3 / 8000000 : ℚ) : ℝ) <
      ((629521681653 / 1000000000000 : ℚ) : ℝ) := Rat.cast_lt.mpr final_arith
  push_cast at hfin
  linarith

end D4Bound
