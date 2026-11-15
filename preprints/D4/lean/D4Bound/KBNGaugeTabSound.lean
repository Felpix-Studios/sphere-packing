import D4Bound.KBNGaugeBound
import D4Bound.CyclicNativeGaugeTab

/-!
# Soundness of the gauge tables

`gaugeAllOK` collects the finite checks (scalar segments on cells 5-6, cell indicator and cap
cut-off decisions, every table entry below its certified value). Given `scalarCheck = true` and
`gaugeAllOK = true` (both by `native_decide` in `KBNGaugeCheck`), `gaugeLoDy_sound` bounds the
gauge weight below on any dyadic box of a region's unit coordinate. Standard axioms only.
-/

namespace D4Bound.KBN
open V7 GaugeTab

def gaugeAllOK : Bool :=
  scalarCheck56 && (List.range 7).all fun k =>
    cellOK k && (decide (5 ≤ k) || capsCutOK k) && tabOK k (gaugeDepth k) (gaugeTabList k)

theorem minRange_le (tab : Array ℚ) (base : ℕ) :
    ∀ (n : ℕ) (acc : ℚ), minRange tab base n acc ≤ acc ∧
      ∀ i < n, minRange tab base n acc ≤ tab.getD (base + i) 0
  | 0, acc => ⟨le_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, acc => by
    obtain ⟨h1, h2⟩ := minRange_le tab base n (min acc (tab.getD (base + n) 0))
    refine ⟨le_trans h1 (min_le_left _ _), fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact h2 i hi
    · subst hi; exact le_trans h1 (min_le_right _ _)

/-- Value at a leaf index is a valid lower bound (inside the table by `tab_sound`, outside 0). -/
theorem leaf_sound (hs : scalarCheck = true) (ha : gaugeAllOK = true) {k : ℕ} (hk : k < 7)
    {r : ℝ} (hr : InCell k r) {j : ℕ}
    (hj1 : (cellLo k : ℝ) + gridW k (gaugeDepth k) * j ≤ r)
    (hj2 : r ≤ (cellLo k : ℝ) + gridW k (gaugeDepth k) * (j + 1)) :
    (((gaugeTab k).getD j 0 : ℚ) : ℝ) ≤ gaugeWeight r := by
  simp only [gaugeAllOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ha
  obtain ⟨hs56, hall⟩ := ha
  have hk' := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk'
  obtain ⟨⟨hok, hcut⟩, htab⟩ := hk'
  have hrr := cell_range hr hk
  have hgw : 0 ≤ gaugeWeight r := by
    have hn := ungaugedPair_nonpos hrr.1 hrr.2
    obtain ⟨p0, p1⟩ := psiQ_range k
    have p1' : (0 : ℝ) < 1 - psiQ k := by
      have : (psiQ k : ℝ) < 1 := by exact_mod_cast p1
      linarith
    unfold gaugeWeight; rw [gaugePsi_cell hok hr]
    exact div_nonneg (by linarith) p1'.le
  have hlen : (gaugeTabList k).length = 2 ^ gaugeDepth k := by
    simp only [tabOK, tabOKU, Bool.and_eq_true, decide_eq_true_eq] at htab; exact htab.1
  unfold gaugeTab
  by_cases hj : j < 2 ^ gaugeDepth k
  · have hget : (gaugeTabList k).toArray.getD j 0 = (gaugeTabList k).getD j 0 := by
      simp [Array.getD, List.getD, hlen, hj]
    rw [hget]
    exact tab_sound hs hs56 htab hk hok (fun h => hcut.resolve_left (by omega)) hj hr hj1 hj2
  · have hget : (gaugeTabList k).toArray.getD j 0 = 0 := by
      simp [Array.getD, hlen, hj]
    rw [hget]; simpa using hgw

theorem gaugeLoDy_sound (hs : scalarCheck = true) (ha : gaugeAllOK = true) {k num lev : ℕ}
    (hk : k < 7) {r : ℝ} (hr : RegionOwns k r)
    (h1 : ((breaks.getD k 0 + (breaks.getD (k + 1) 0 - breaks.getD k 0) *
      ((num : ℚ) / (2 ^ lev : ℕ)) : ℚ) : ℝ) ≤ r)
    (h2 : r ≤ ((breaks.getD k 0 + (breaks.getD (k + 1) 0 - breaks.getD k 0) *
      (((num + 1 : ℕ) : ℚ) / (2 ^ lev : ℕ)) : ℚ) : ℝ)) :
    (gaugeLoDy (gaugeTab k) (gaugeDepth k) num lev : ℝ) ≤ gaugeWeight r := by
  have hc := inCell_of_regionOwns hr
  have hlo : breaks.getD k 0 = cellLo k := by interval_cases k <;> rfl
  have hhi : breaks.getD (k + 1) 0 = cellHi k := by interval_cases k <;> rfl
  rw [hlo, hhi] at h1 h2
  push_cast at h1 h2
  have hw : (0 : ℝ) < (cellHi k : ℝ) - cellLo k := by
    have : cellLo k < cellHi k := by interval_cases k <;> simp [cellLo, cellHi, breaks] <;> norm_num
    have : ((cellLo k : ℚ) : ℝ) < ((cellHi k : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  have hgW : (gridW k (gaugeDepth k) : ℝ) = ((cellHi k : ℝ) - cellLo k) / 2 ^ gaugeDepth k := by
    unfold gridW; push_cast; rfl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (r - cellLo k) / ((cellHi k : ℝ) - cellLo k) := ⟨_, rfl⟩
  have hrx : r = (cellLo k : ℝ) + ((cellHi k : ℝ) - cellLo k) * x := by
    rw [hx]; field_simp; ring
  have hp : (0 : ℝ) < 2 ^ lev := by positivity
  have hx0 : (num : ℝ) ≤ x * 2 ^ lev := by
    have : (num : ℝ) / 2 ^ lev ≤ x := by rw [hx, le_div_iff₀ hw]; linarith
    rwa [div_le_iff₀ hp] at this
  have hx1 : x * 2 ^ lev ≤ (num : ℝ) + 1 := by
    have : x ≤ ((num : ℝ) + 1) / 2 ^ lev := by rw [hx, div_le_iff₀ hw]; linarith
    rwa [le_div_iff₀ hp] at this
  have leaf : ∀ j : ℕ, (j : ℝ) ≤ x * 2 ^ gaugeDepth k → x * 2 ^ gaugeDepth k ≤ (j : ℝ) + 1 →
      (((gaugeTab k).getD j 0 : ℚ) : ℝ) ≤ gaugeWeight r := by
    intro j a b
    have hpD : (0 : ℝ) < 2 ^ gaugeDepth k := by positivity
    have a' : (j : ℝ) / 2 ^ gaugeDepth k ≤ x := by rw [div_le_iff₀ hpD]; exact a
    have b' : x ≤ ((j : ℝ) + 1) / 2 ^ gaugeDepth k := by rw [le_div_iff₀ hpD]; exact b
    apply leaf_sound hs ha hk hc
    · rw [hgW, hrx]
      have : ((cellHi k : ℝ) - cellLo k) / 2 ^ gaugeDepth k * j =
          ((cellHi k : ℝ) - cellLo k) * ((j : ℝ) / 2 ^ gaugeDepth k) := by ring
      rw [this]; nlinarith
    · rw [hgW, hrx]
      have : ((cellHi k : ℝ) - cellLo k) / 2 ^ gaugeDepth k * (j + 1) =
          ((cellHi k : ℝ) - cellLo k) * (((j : ℝ) + 1) / 2 ^ gaugeDepth k) := by ring
      rw [this]; nlinarith
  unfold gaugeLoDy
  by_cases hD : gaugeDepth k ≤ lev
  · rw [if_pos hD]
    obtain ⟨m, hm⟩ : ∃ m, lev = gaugeDepth k + m := ⟨lev - gaugeDepth k, by omega⟩
    have hmm : lev - gaugeDepth k = m := by omega
    rw [hmm]
    have hlev : (2 : ℝ) ^ lev = 2 ^ gaugeDepth k * 2 ^ m := by rw [hm, pow_add]
    have hm0 : 0 < 2 ^ m := Nat.pow_pos (by norm_num)
    have hj1 : num / 2 ^ m * 2 ^ m ≤ num := Nat.div_mul_le_self num (2 ^ m)
    have hj2 : num < (num / 2 ^ m + 1) * 2 ^ m := by
      have := Nat.lt_div_mul_add (a := num) hm0; rw [add_mul, one_mul]; exact this
    have hj1' : ((num / 2 ^ m : ℕ) : ℝ) * 2 ^ m ≤ num := by exact_mod_cast hj1
    have hj2' : (num : ℝ) + 1 ≤ (((num / 2 ^ m : ℕ) : ℝ) + 1) * 2 ^ m := by exact_mod_cast hj2
    have hpm : (0 : ℝ) < 2 ^ m := by positivity
    rw [hlev] at hx0 hx1
    apply leaf
    · have : ((num / 2 ^ m : ℕ) : ℝ) * 2 ^ m ≤ x * 2 ^ gaugeDepth k * 2 ^ m := by nlinarith
      exact le_of_mul_le_mul_right this hpm
    · have : x * 2 ^ gaugeDepth k * 2 ^ m ≤ (((num / 2 ^ m : ℕ) : ℝ) + 1) * 2 ^ m := by nlinarith
      exact le_of_mul_le_mul_right this hpm
  · rw [if_neg hD]
    obtain ⟨m, hm⟩ : ∃ m, gaugeDepth k = lev + m := ⟨gaugeDepth k - lev, by omega⟩
    have hmm : gaugeDepth k - lev = m := by omega
    rw [hmm]
    have hDl : (2 : ℝ) ^ gaugeDepth k = 2 ^ lev * 2 ^ m := by rw [hm, pow_add]
    have hpm : (0 : ℝ) < 2 ^ m := by positivity
    have hm0 : 0 < 2 ^ m := Nat.pow_pos (by norm_num)
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (x * 2 ^ lev - num) * 2 ^ m := ⟨_, rfl⟩
    have hy0 : 0 ≤ y := by rw [hy]; apply mul_nonneg _ hpm.le; linarith
    have hym : y ≤ 2 ^ m := by
      rw [hy]
      have : x * 2 ^ lev - num ≤ 1 := by linarith
      nlinarith
    obtain ⟨i, hidef⟩ : ∃ i, i = min (⌊y⌋₊) (2 ^ m - 1) := ⟨_, rfl⟩
    have hi_lt : i < 2 ^ m := by omega
    have hiy : (i : ℝ) ≤ y := by
      have : i ≤ ⌊y⌋₊ := by rw [hidef]; exact min_le_left _ _
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hy0)
    have hyi : y ≤ (i : ℝ) + 1 := by
      by_cases hf : ⌊y⌋₊ ≤ 2 ^ m - 1
      · have : i = ⌊y⌋₊ := by rw [hidef]; exact min_eq_left hf
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · have : i = 2 ^ m - 1 := by rw [hidef]; exact min_eq_right (by omega)
        rw [this]
        have : ((2 ^ m - 1 : ℕ) : ℝ) + 1 = 2 ^ m := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; exact hym
    obtain ⟨_, hmin⟩ := minRange_le (gaugeTab k) (num * 2 ^ m) (2 ^ m)
      ((gaugeTab k).getD (num * 2 ^ m) 0)
    have hle := hmin i hi_lt
    have hle' : ((minRange (gaugeTab k) (num * 2 ^ m) (2 ^ m)
        ((gaugeTab k).getD (num * 2 ^ m) 0) : ℚ) : ℝ) ≤
        (((gaugeTab k).getD (num * 2 ^ m + i) 0 : ℚ) : ℝ) := by exact_mod_cast hle
    refine le_trans hle' (leaf (num * 2 ^ m + i) ?_ ?_)
    · rw [hDl]; push_cast
      have : x * (2 ^ lev * 2 ^ m) = num * 2 ^ m + y := by rw [hy]; ring
      rw [this]; linarith
    · rw [hDl]; push_cast
      have : x * (2 ^ lev * 2 ^ m) = num * 2 ^ m + y := by rw [hy]; ring
      rw [this]; linarith

end D4Bound.KBN
