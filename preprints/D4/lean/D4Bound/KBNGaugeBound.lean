import D4Bound.PairNativeOutside

/-!
# Gauge-weight lower bounds on every radial piece

`gaugeWeight r = -ungaugedPair r / (1 - psi r)` is bounded below on a dyadic grid of each
radial cell. On cells 0-4 the bound uses `Upoly ghat k` (`ungauged_le`); on cells 5-6 it uses
`ungaugedPair_le_upper` (diagonal source with uncut caps) and new upper polynomials
`ghat5`, `ghat6` for `scalarRadius`, proved on segments where `2 r²` stays within 1 of an
integer `K` (exp re-centred at `exp (-K) = exp (-1) ^ K`). `tab_sound` turns a table check into
`tab[j] ≤ gaugeWeight r` for every `r` in grid cell `j`. Standard axioms only; the Boolean
checks are run by `native_decide` in `KBNGaugeCheck`.
-/

namespace D4Bound.KBN
open V7

/-! ## Scalar part on a segment, exp re-centred at an integer -/

def wPK (K : ℕ) : P1 := [(K : ℚ) - 2, -4, -2]
def TPK (K n : ℕ) : P1 :=
  psum qAlg ((List.range n).map fun i => A1.smul (1 / (Nat.factorial i : ℚ)) (ppow qAlg (wPK K) i))
def GPK (K n : ℕ) : P1 := A1.mul (TPK K n) FcP
def aL : ℚ := aQ - d1Q
def aU : ℚ := aQ + d1Q
def xmSeg (K : ℕ) (ulo uhi : ℚ) : ℚ :=
  max |(K : ℚ) - 2 * (1 + ulo) ^ 2| |(K : ℚ) - 2 * (1 + uhi) ^ 2|
def rhoSeg (n : ℕ) (xm : ℚ) : ℚ := xm ^ n * (((n : ℚ) + 1) / ((Nat.factorial n : ℚ) * n))
def errSeg (K n : ℕ) (ulo uhi : ℚ) : ℚ :=
  (aU ^ K - aL ^ K) * abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) (GPK K n)) +
  aU ^ K * rhoSeg n (xmSeg K ulo uhi) * abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) FcP)
def gapSeg (g : P1) (K n : ℕ) (ulo uhi : ℚ) : P1 :=
  A1.add g (A1.add (A1.smul (-(aQ ^ K)) (GPK K n)) [-(errSeg K n ulo uhi)])

def segCheck (g : P1) (K n : ℕ) (ulo uhi : ℚ) (fuel : ℕ) : Bool :=
  search1 (gapSeg g K n ulo uhi) fuel ((ulo + uhi) / 2) ((uhi - ulo) / 2) &&
    decide (xmSeg K ulo uhi ≤ 1) && decide (0 ≤ aL) && decide (0 < n) && decide (-1 ≤ ulo) &&
    decide (ulo ≤ uhi)

theorem E1_TPK (K n : ℕ) (r : ℝ) : E1 (TPK K n) (r - 1) =
    ∑ m ∈ Finset.range n, ((K : ℝ) - 2 * r ^ 2) ^ m / (m.factorial : ℝ) := by
  unfold TPK
  rw [E1_psum, List.map_map, ← list_range_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, E1_smul, E1_ppow]
  have : E1 (wPK K) (r - 1) = (K : ℝ) - 2 * r ^ 2 := by
    simp only [wPK, E1, peval_cons, peval_nil]; push_cast; ring
  rw [this]
  push_cast; ring

theorem segCheck_sound {g : P1} {K n : ℕ} {ulo uhi : ℚ} {fuel : ℕ}
    (hc : segCheck g K n ulo uhi fuel = true) {r : ℝ} (h1 : (ulo : ℝ) ≤ r - 1)
    (h2 : r - 1 ≤ (uhi : ℝ)) : scalarRadius r ≤ E1 g (r - 1) := by
  simp only [segCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hs, hxm⟩, haL⟩, hn⟩, hu0⟩, hlu⟩ := hc
  have hu0' : (-1 : ℝ) ≤ ulo := by exact_mod_cast hu0
  have hu : |(r - 1) - (((ulo + uhi) / 2 : ℚ) : ℝ)| ≤ (((uhi - ulo) / 2 : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith
  have hgap := search1_sound _ fuel _ _ hs (r - 1) hu
  simp only [gapSeg, E1_add, E1_smul, E1_singleton] at hgap
  -- range of x = K - 2 r²
  have hr0 : 0 ≤ 1 + (ulo : ℝ) := by linarith
  have hxabs : |(K : ℝ) - 2 * r ^ 2| ≤ (xmSeg K ulo uhi : ℝ) := by
    unfold xmSeg
    push_cast
    have hA : (K : ℝ) - 2 * r ^ 2 ≤ (K : ℝ) - 2 * (1 + ulo) ^ 2 := by nlinarith
    have hB : (K : ℝ) - 2 * (1 + uhi) ^ 2 ≤ (K : ℝ) - 2 * r ^ 2 := by nlinarith
    rw [abs_le]; constructor
    · have := neg_abs_le ((K : ℝ) - 2 * (1 + uhi) ^ 2)
      have := le_max_right |(K : ℝ) - 2 * (1 + ulo) ^ 2| |(K : ℝ) - 2 * (1 + uhi) ^ 2|
      linarith
    · have := le_abs_self ((K : ℝ) - 2 * (1 + ulo) ^ 2)
      have := le_max_left |(K : ℝ) - 2 * (1 + ulo) ^ 2| |(K : ℝ) - 2 * (1 + uhi) ^ 2|
      linarith
  have hx1 : |(K : ℝ) - 2 * r ^ 2| ≤ 1 := le_trans hxabs (by exact_mod_cast hxm)
  have hT := Real.exp_bound hx1 (n := n) hn
  rw [← E1_TPK] at hT
  have hrho : |(K : ℝ) - 2 * r ^ 2| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) ≤
      (rhoSeg n (xmSeg K ulo uhi) : ℝ) := by
    unfold rhoSeg
    push_cast
    apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hxabs _)
    positivity
  -- exp(-1) enclosure
  have hE := Real.exp_bound (x := -1) (by norm_num) (n := em) (by norm_num [em])
  rw [← aQ_cast] at hE
  simp only [abs_neg, abs_one, one_pow, one_mul] at hE
  have hd1 : ((em.succ : ℝ) / ((em.factorial : ℝ) * em)) = (d1Q : ℝ) := by
    unfold d1Q; push_cast; ring
  rw [hd1] at hE
  obtain ⟨hE1, hE2⟩ := abs_le.mp hE
  have haL' : (0 : ℝ) ≤ aL := by exact_mod_cast haL
  have hlo : (aL : ℝ) ≤ Real.exp (-1) := by unfold aL; push_cast; linarith
  have hhi : Real.exp (-1) ≤ (aU : ℝ) := by unfold aU; push_cast; linarith
  have hd0 : (0 : ℝ) ≤ d1Q := by unfold d1Q; positivity
  have haQ1 : (aL : ℝ) ≤ aQ := by unfold aL; push_cast; linarith
  have haQ2 : (aQ : ℝ) ≤ aU := by unfold aU; push_cast; linarith
  have heK1 := pow_le_pow_left₀ haL' hlo K
  have heK2 := pow_le_pow_left₀ (le_trans haL' hlo) hhi K
  have haK1 := pow_le_pow_left₀ haL' haQ1 K
  have haK2 := pow_le_pow_left₀ (le_trans haL' haQ1) haQ2 K
  have heps : |Real.exp (-1) ^ K - (aQ : ℝ) ^ K| ≤ (aU : ℝ) ^ K - (aL : ℝ) ^ K := by
    rw [abs_le]; constructor <;> linarith
  have hexp2 : Real.exp (-2 * r ^ 2) = Real.exp (-1) ^ K * Real.exp ((K : ℝ) - 2 * r ^ 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hG : |E1 (GPK K n) (r - 1)| ≤
      (abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) (GPK K n)) : ℝ) := by
    have := (bounds1 hu (pshift qAlg ((ulo + uhi) / 2) (GPK K n))).2
    rwa [E1_pshift, add_sub_cancel] at this
  have hF : |E1 FcP (r - 1)| ≤
      (abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) FcP) : ℝ) := by
    have := (bounds1 hu (pshift qAlg ((ulo + uhi) / 2) FcP)).2
    rwa [E1_pshift, add_sub_cancel] at this
  have hGe : E1 (GPK K n) (r - 1) = E1 (TPK K n) (r - 1) * F (2 * r ^ 2) := by
    rw [GPK, E1_mul, E1_FcP]
  have he0 : 0 ≤ Real.exp (-1) ^ K := by positivity
  have hsr : scalarRadius r = Real.exp (-1) ^ K * (E1 (TPK K n) (r - 1) * F (2 * r ^ 2)) +
      Real.exp (-1) ^ K * ((Real.exp ((K : ℝ) - 2 * r ^ 2) - E1 (TPK K n) (r - 1)) * F (2 * r ^ 2)) := by
    unfold scalarRadius; rw [hexp2]; ring
  rw [hsr]
  rw [E1_FcP] at hF
  rw [hGe] at hG hgap
  have herr : (errSeg K n ulo uhi : ℝ) =
      ((aU : ℝ) ^ K - (aL : ℝ) ^ K) * (abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) (GPK K n)) : ℝ) +
      (aU : ℝ) ^ K * (rhoSeg n (xmSeg K ulo uhi) : ℝ) *
        (abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) FcP) : ℝ) := by
    unfold errSeg; push_cast; ring
  push_cast at hgap
  rw [herr] at hgap
  have hδb := le_trans hT hrho
  generalize (abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) (GPK K n)) : ℝ) = MG at hG hgap
  generalize (abs1 ((uhi - ulo) / 2) (pshift qAlg ((ulo + uhi) / 2) FcP) : ℝ) = MF at hF hgap
  generalize E1 (TPK K n) (r - 1) = T at hδb hG hgap ⊢
  generalize F (2 * r ^ 2) = Fv at hF hG hgap ⊢
  generalize Real.exp ((K : ℝ) - 2 * r ^ 2) - T = δ at hδb ⊢
  generalize Real.exp (-1) ^ K = e at heps heK2 he0 ⊢
  have hepsE : (0 : ℝ) ≤ (aU : ℝ) ^ K - (aL : ℝ) ^ K := le_trans (abs_nonneg _) heps
  have hrho0 : (0 : ℝ) ≤ rhoSeg n (xmSeg K ulo uhi) := le_trans (abs_nonneg _) hδb
  have k1 : e * (T * Fv) ≤ (aQ : ℝ) ^ K * (T * Fv) + ((aU : ℝ) ^ K - (aL : ℝ) ^ K) * MG := by
    have h3 : |(e - (aQ : ℝ) ^ K) * (T * Fv)| ≤ ((aU : ℝ) ^ K - (aL : ℝ) ^ K) * MG := by
      rw [abs_mul]; exact mul_le_mul heps hG (abs_nonneg _) hepsE
    have := le_abs_self ((e - (aQ : ℝ) ^ K) * (T * Fv))
    nlinarith
  have k2 : e * (δ * Fv) ≤ (aU : ℝ) ^ K * (rhoSeg n (xmSeg K ulo uhi) : ℝ) * MF := by
    have h3 : |δ * Fv| ≤ (rhoSeg n (xmSeg K ulo uhi) : ℝ) * MF := by
      rw [abs_mul]; exact mul_le_mul hδb hF (abs_nonneg _) hrho0
    have h5 : (0 : ℝ) ≤ rhoSeg n (xmSeg K ulo uhi) * MF := le_trans (abs_nonneg _) h3
    have h4 : e * (δ * Fv) ≤ e * (rhoSeg n (xmSeg K ulo uhi) * MF) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h3) he0
    have h6 : e * ((rhoSeg n (xmSeg K ulo uhi) : ℝ) * MF) ≤ (aU : ℝ) ^ K * (rhoSeg n (xmSeg K ulo uhi) * MF) :=
      mul_le_mul_of_nonneg_right heK2 h5
    nlinarith
  linarith

/-! ## Ungauged source on cells 5 and 6 (uncut caps, no self caps) -/

def linPU (k : ℕ) : P1 :=
  A1.add (rvP originVector k) (A1.add
    (psum qAlg (caps.map fun c => A1.smul (c.weight * c.multiplicity / 2) (rvP c.vector k)))
    (A1.add (psum qAlg (tents.map fun c => A1.smul (c.weight * c.capacity / 2) (rvP c.vector k)))
      (A1.add (psum qAlg (allocations.map fun c => A1.smul (c.weight / 2) (rvP c.vector k)))
        [(sphericalRays.map fun c => c.weight * c.bound * indQ k c.radius / 2).sum +
         (conditionalRays.map fun c => 23 * c.weight * (indQ k c.outer - indQ k c.inner) / 2).sum +
         (countPolynomials.map fun c => c.weight * ((List.range c.radii.length).map fun i =>
            c.linear.getD i 0 * indQ k (c.radii.getD i 0)).sum).sum])))

structure RadOK (k : ℕ) (r : ℝ) : Prop where
  hr : InCell k r
  pr : radialPiece r = k
  k7 : k < 7
  ok : cellOK k = true

theorem E1_linPU {k : ℕ} {r : ℝ} (h : RadOK k r) : E1 (linPU k) (r - 1) = uncutLinear r := by
  unfold linPU uncutLinear
  simp only [E1_add, E1_psum, List.map_map, E1_singleton]
  simp only [Function.comp_def]
  rw [E1_rvP _ h.pr h.k7]
  have hc : ((caps.map fun c => E1 (A1.smul (c.weight * c.multiplicity / 2)
      (rvP c.vector k)) (r - 1))) =
      (caps.map fun c => (c.weight : ℝ) * (c.multiplicity : ℝ) * radialValue c.vector r / 2) := by
    apply List.map_congr_left
    intro c hc
    rw [E1_smul, E1_rvP _ h.pr h.k7]
    push_cast; ring
  have ht : ((tents.map fun c => E1 (A1.smul (c.weight * c.capacity / 2) (rvP c.vector k)) (r - 1))) =
      (tents.map fun c => (c.weight : ℝ) * (c.capacity : ℝ) * radialValue c.vector r / 2) := by
    apply List.map_congr_left
    intro c _
    rw [E1_smul, E1_rvP _ h.pr h.k7]
    push_cast; ring
  have ha : ((allocations.map fun c => E1 (A1.smul (c.weight / 2) (rvP c.vector k)) (r - 1))) =
      (allocations.map fun c => (c.weight : ℝ) * radialValue c.vector r / 2) := by
    apply List.map_congr_left
    intro c _
    rw [E1_smul, E1_rvP _ h.pr h.k7]
    push_cast; ring
  have hs : (sphericalRays.map fun c => (c.weight : ℝ) * (c.bound : ℝ) * indicator c.radius r / 2) =
      (sphericalRays.map fun c => (c.weight : ℝ) * (c.bound : ℝ) * (indQ k c.radius : ℝ) / 2) := by
    apply List.map_congr_left
    intro c hc
    have hR : c.radius ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl (Or.inl ⟨c, hc, rfl⟩))
    rw [ind_of_mem h.ok h.hr hR]
  have hd : (conditionalRays.map fun c => 23 * (c.weight : ℝ) *
      (indicator c.outer r - indicator c.inner r) / 2) =
      (conditionalRays.map fun c => 23 * (c.weight : ℝ) *
      ((indQ k c.outer : ℝ) - (indQ k c.inner : ℝ)) / 2) := by
    apply List.map_congr_left
    intro c hc
    have hi : c.inner ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact Or.inr (Or.inl (Or.inr ⟨c, hc, by simp⟩))
    have ho : c.outer ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact Or.inr (Or.inl (Or.inr ⟨c, hc, by simp⟩))
    rw [ind_of_mem h.ok h.hr hi, ind_of_mem h.ok h.hr ho]
  have hn : (countPolynomials.map fun c => countLinear c r) =
      (countPolynomials.map fun c => (c.weight : ℝ) * ((List.range c.radii.length).map fun i =>
        ((c.linear.getD i 0 : ℚ) : ℝ) * (indQ k (c.radii.getD i 0) : ℝ)).sum) := by
    apply List.map_congr_left
    intro c hc
    unfold countLinear
    congr 2
    apply List.map_congr_left
    intro i hi
    have hR : c.radii.getD i 0 ∈ allRadii := by
      simp only [allRadii, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
      exact Or.inr (Or.inr ⟨c, hc, i, hi, rfl⟩)
    rw [ind_of_mem h.ok h.hr hR]
  rw [hc, ht, ha, hs, hd, hn]
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat, cast_sum_map]
  ring

def ghat5 : P1 := [(168353386613690129599558174953249 / 1298074214633706907132624082305024 : ℚ), (-969853186017747809035499531807511 / 1298074214633706907132624082305024 : ℚ), (2057666040692524251304971979549865 / 1298074214633706907132624082305024 : ℚ), (-1500337925563665627593324007203025 / 1298074214633706907132624082305024 : ℚ), (-515214598713988504443358851559707 / 649037107316853453566312041152512 : ℚ), (1118522202778668614665426873234017 / 649037107316853453566312041152512 : ℚ), (-490180802553911412973637292914513 / 1298074214633706907132624082305024 : ℚ), (-1154275172859607067881763149771323 / 1298074214633706907132624082305024 : ℚ), (300900083794692517306762946720929 / 649037107316853453566312041152512 : ℚ), (383520852119092515305613761681339 / 1298074214633706907132624082305024 : ℚ), (-201056795507186926119277215980251 / 1298074214633706907132624082305024 : ℚ), (-86794674542486486678340763589497 / 324518553658426726783156020576256 : ℚ), (-108326960415462063540499642302045 / 1298074214633706907132624082305024 : ℚ), (1038043330498951553505036417081491 / 1298074214633706907132624082305024 : ℚ), (-944481281003086424474472596554819 / 1298074214633706907132624082305024 : ℚ), (1165773239259217082688748561221519 / 649037107316853453566312041152512 : ℚ), (-5281892953271033977414858801818969 / 649037107316853453566312041152512 : ℚ), (12977509556965080065949521416781113 / 649037107316853453566312041152512 : ℚ), (-22428314262786426091259317516608667 / 649037107316853453566312041152512 : ℚ), (63817818601844179608953381366750031 / 1298074214633706907132624082305024 : ℚ), (-73326225245533862612008591067485361 / 1298074214633706907132624082305024 : ℚ), (3864514845705095171832546202393097 / 81129638414606681695789005144064 : ℚ), (-34743176810240296721711614937549257 / 1298074214633706907132624082305024 : ℚ), (179914882370818642922879391144305 / 20282409603651670423947251286016 : ℚ), (-1701642880687488141825398179847303 / 1298074214633706907132624082305024 : ℚ)]
def ghat6 : P1 := [(168469068846968354176394885856547 / 1298074214633706907132624082305024 : ℚ), (-486874124131416111868043299432707 / 649037107316853453566312041152512 : ℚ), (529969334839899614265895674976577 / 324518553658426726783156020576256 : ℚ), (-2126890952468230538912235132639843 / 1298074214633706907132624082305024 : ℚ), (1715392164289146958928413187229359 / 649037107316853453566312041152512 : ℚ), (-21624757613209955253269952769009887 / 1298074214633706907132624082305024 : ℚ), (98939107926182713430164968221886557 / 1298074214633706907132624082305024 : ℚ), (-165724496260024559421498127096820839 / 649037107316853453566312041152512 : ℚ), (888239894755972682736966333185037075 / 1298074214633706907132624082305024 : ℚ), (-973202677767892383236355844803758707 / 649037107316853453566312041152512 : ℚ), (3498755222858238835225965367953828613 / 1298074214633706907132624082305024 : ℚ), (-5154227371348986737861685747216121141 / 1298074214633706907132624082305024 : ℚ), (387389335168993185114994479145027433 / 81129638414606681695789005144064 : ℚ), (-3019265197221309113515246057261603683 / 649037107316853453566312041152512 : ℚ), (2355006962259840126459509703078781895 / 649037107316853453566312041152512 : ℚ), (-2891144393083966119819916795104067945 / 1298074214633706907132624082305024 : ℚ), (85127168434674473438139082718991423 / 81129638414606681695789005144064 : ℚ), (-474097320891595524917362054407086479 / 1298074214633706907132624082305024 : ℚ), (57291390385121470297946403420712901 / 649037107316853453566312041152512 : ℚ), (-2140302964400221299732185895826669 / 162259276829213363391578010288128 : ℚ), (593763995834190571021908971458699 / 649037107316853453566312041152512 : ℚ)]

def UpolyU (g : P1) (k : ℕ) : P1 :=
  A1.add g (A1.add (A1.smul 2 (linPU k)) (diag3 (coreP k k)))

theorem ungauged_le_U {g : P1} {k : ℕ} {r : ℝ} (h : RadOK k r)
    (hg : scalarRadius r ≤ E1 g (r - 1)) : ungaugedPair r ≤ E1 (UpolyU g k) (r - 1) := by
  have hr := cell_range h.hr h.k7
  have hcp : CellPair k k r r := ⟨h.hr, h.hr, h.pr, h.pr, h.k7, h.k7, h.ok, h.ok⟩
  have hcore : E1 (diag3 (coreP k k)) (r - 1) = corePair r r 1 := by
    rw [E1_diag3]; exact E3_coreP hcp 1
  have hU := ungaugedPair_le_upper hr.1 hr.2
  have e : diagonalUpper r = 2 * uncutLinear r + corePair r r 1 := by
    unfold diagonalUpper corePair; ring
  unfold UpolyU
  simp only [E1_add, E1_smul, hcore, E1_linPU h]
  rw [e] at hU
  push_cast
  linarith

/-- The polynomial used on cell `k`. -/
def Ugen (k : ℕ) : P1 :=
  if k < 5 then Upoly ghat k else if k = 5 then UpolyU ghat5 5 else UpolyU ghat6 6

/-- Scalar segment checks for cells 5 and 6. -/
def scalarCheck56 : Bool :=
  segCheck ghat5 3 24 (2597 / 100000) (2 / 5) 16 && segCheck ghat5 4 20 (2 / 5) (1 / 2) 16 &&
  segCheck ghat6 5 22 (1 / 2) (7 / 10) 16 && segCheck ghat6 6 20 (7 / 10) (3 / 4) 16

theorem ungauged_le_gen (hs : scalarCheck = true) (hs56 : scalarCheck56 = true) {k : ℕ} {r : ℝ}
    (hk : k < 7) (hr : InCell k r) (hok : cellOK k = true) (hcut : k < 5 → capsCutOK k = true) :
    ungaugedPair r ≤ E1 (Ugen k) (r - 1) := by
  have pr := radialPiece_cell7 hr hk
  obtain ⟨h1, h2, h3⟩ := hr
  unfold Ugen
  by_cases h5 : k < 5
  · rw [if_pos h5]
    exact ungauged_le (scalar_upper_of_check hs) ⟨⟨h1, h2, h3⟩, pr, hk, hok, hcut h5⟩ h5
  · rw [if_neg h5]
    simp only [scalarCheck56, Bool.and_eq_true] at hs56
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hs56
    by_cases h55 : k = 5
    · subst h55
      rw [if_pos rfl]
      have hb1 : (102597 / 100000 : ℝ) ≤ r := by simpa [cellLo, breaks] using h1
      have hb2 : r ≤ 3 / 2 := by simpa [cellHi, breaks] using h2
      apply ungauged_le_U ⟨⟨h1, h2, h3⟩, pr, hk, hok⟩
      by_cases hm : r - 1 ≤ ((2 / 5 : ℚ) : ℝ)
      · exact segCheck_sound a (by push_cast; linarith) hm
      · exact segCheck_sound b (by push_cast at hm ⊢; linarith) (by push_cast; linarith)
    · have h66 : k = 6 := by omega
      subst h66
      rw [if_neg (by norm_num)]
      have hb1 : (3 / 2 : ℝ) ≤ r := by simpa [cellLo, breaks] using h1
      have hb2 : r ≤ 7 / 4 := by simpa [cellHi, breaks] using h2
      apply ungauged_le_U ⟨⟨h1, h2, h3⟩, pr, hk, hok⟩
      by_cases hm : r - 1 ≤ ((7 / 10 : ℚ) : ℝ)
      · exact segCheck_sound c (by push_cast; linarith) hm
      · exact segCheck_sound d (by push_cast at hm ⊢; linarith) (by push_cast; linarith)

/-! ## Grid tables -/

def gridW (k D : ℕ) : ℚ := (cellHi k - cellLo k) / 2 ^ D

def certValU (U : P1) (k D j : ℕ) : ℚ :=
  max 0 (low1 (gridW k D / 2)
    (pshift qAlg (cellLo k + gridW k D * ((j : ℚ) + 1 / 2) - 1) (A1.smul (-1) U)) /
    (1 - psiQ k))

def certVal (k D j : ℕ) : ℚ := certValU (Ugen k) k D j

theorem certVal_le (hs : scalarCheck = true) (hs56 : scalarCheck56 = true) {k D j : ℕ}
    (hk : k < 7) (hok : cellOK k = true) (hcut : k < 5 → capsCutOK k = true) {r : ℝ}
    (hr : InCell k r) (hj1 : (cellLo k : ℝ) + gridW k D * j ≤ r)
    (hj2 : r ≤ (cellLo k : ℝ) + gridW k D * (j + 1)) : (certVal k D j : ℝ) ≤ gaugeWeight r := by
  have hU := ungauged_le_gen hs hs56 hk hr hok hcut
  have hbox : |(r - 1) - (((cellLo k + gridW k D * ((j : ℚ) + 1 / 2) - 1 : ℚ)) : ℝ)| ≤
      ((gridW k D / 2 : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith
  have hl := low1_shift_sound hbox (A1.smul (-1) (Ugen k))
  rw [E1_smul] at hl
  push_cast at hl
  have hps := gaugePsi_cell hok hr
  obtain ⟨p0, p1⟩ := psiQ_range k
  have p1' : (0 : ℝ) < 1 - psiQ k := by
    have : (psiQ k : ℝ) < 1 := by exact_mod_cast p1
    linarith
  have hrr := cell_range hr hk
  have hn := ungaugedPair_nonpos hrr.1 hrr.2
  unfold gaugeWeight
  rw [hps]
  unfold certVal certValU
  push_cast
  apply max_le
  · exact div_nonneg (by linarith) p1'.le
  · exact div_le_div_of_nonneg_right (by linarith) p1'.le

/-- A table is valid when it has `2^D` entries, each below the certified value. -/
def tabOKU (U : P1) (k D : ℕ) (tab : List ℚ) : Bool :=
  decide (tab.length = 2 ^ D) &&
    (List.range (2 ^ D)).all fun j => decide (tab.getD j 0 ≤ certValU U k D j)

def tabOK (k D : ℕ) (tab : List ℚ) : Bool := tabOKU (Ugen k) k D tab

theorem tab_sound (hs : scalarCheck = true) (hs56 : scalarCheck56 = true) {k D : ℕ} {tab : List ℚ}
    (ht : tabOK k D tab = true) (hk : k < 7) (hok : cellOK k = true)
    (hcut : k < 5 → capsCutOK k = true) {j : ℕ} (hj : j < 2 ^ D) {r : ℝ} (hr : InCell k r)
    (hj1 : (cellLo k : ℝ) + gridW k D * j ≤ r) (hj2 : r ≤ (cellLo k : ℝ) + gridW k D * (j + 1)) :
    ((tab.getD j 0 : ℚ) : ℝ) ≤ gaugeWeight r := by
  simp only [tabOK, tabOKU, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hv := List.all_eq_true.mp ht.2 j (List.mem_range.mpr hj)
  simp only [decide_eq_true_eq] at hv
  have h1 : ((tab.getD j 0 : ℚ) : ℝ) ≤ (certVal k D j : ℝ) := by
    unfold certVal; exact_mod_cast hv
  exact le_trans h1 (certVal_le hs hs56 hk hok hcut hr hj1 hj2)

end D4Bound.KBN
