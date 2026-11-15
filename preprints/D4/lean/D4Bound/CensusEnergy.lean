import D4Bound.CensusFinite
import D4Bound.Main

/-! The exact interface between the finite census and the analytic energy proof.
This implication alone does not discharge `CensusFloor`: the concrete kernel
must still be shown to dominate the exact arithmetic expression. -/
namespace D4Bound

theorem censusFloor_of_lower {K : E4 → E4 → ℝ}
    (henergy : ∀ X : Finset E4, Admissible X → InCountDomain X →
      (CensusArithmetic.lower (CensusArithmetic.ofNeighbourhood X) : ℝ) ≤
        nbhdEnergy (fun x y => K x y - Kg x y) X) : CensusFloor K := by
  intro X hX hD g hg hN hj
  have hn := CensusArithmetic.numeric_floor (CensusArithmetic.ofNeighbourhood_valid hD)
    hg hN hj
  exact (Rat.cast_le.mpr hn).trans (henergy X hX hD)

end D4Bound
