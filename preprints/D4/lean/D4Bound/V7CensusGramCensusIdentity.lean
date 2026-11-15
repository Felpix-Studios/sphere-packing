import D4Bound.V7CensusCount
namespace D4Bound.V7.CensusGram
open CensusArithmetic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem affine_count_identity (a : List ℚ) (q : ℚ) (c : Array ℤ)
    (hq : q = (c[0]! : ℚ)/(denominator : ℚ))
    (ha : ∀ i, i < 5 → a.getD i 0 = (c[i+1]! : ℚ)/(denominator : ℚ))
    (X : Finset E4) :
    (q : ℝ) + ((List.range 5).map fun i => (a.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (affine c (ofNeighbourhood X) : ℝ)/(denominator : ℝ) := by
  rw [hq]
  have h0 := ha 0 (by omega)
  have h1 := ha 1 (by omega)
  have h2 := ha 2 (by omega)
  have h3 := ha 3 (by omega)
  have h4 := ha 4 (by omega)
  simp only [List.getD_eq_getElem?_getD] at h0 h1 h2 h3 h4
  norm_num [List.range_succ, h0, h1, h2, h3, h4,
    affine, ofNeighbourhood, nearCount, R1, R2, R3, R4, R5, breaks]
  ring
end
end D4Bound.V7.CensusGram
