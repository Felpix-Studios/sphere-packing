import D4Bound.CensusFinite01
import D4Bound.CensusFinite02
import D4Bound.CensusFinite03
import D4Bound.CensusFinite04
import D4Bound.CensusFinite05
import D4Bound.CensusFinite06
import D4Bound.CensusFinite07
import D4Bound.CensusFinite08
import D4Bound.CensusFinite09
import D4Bound.CensusFinite10
import D4Bound.CensusFinite11
import D4Bound.CensusFinite12
import D4Bound.CensusFinite13
import D4Bound.CensusFinite14
import D4Bound.CensusFinite15
import D4Bound.CensusFinite16
import D4Bound.CensusFinite17
import D4Bound.CensusFinite18
import D4Bound.CensusFinite19
import D4Bound.CensusFinite20
import D4Bound.CensusFinite21
import D4Bound.CensusFinite22
import D4Bound.CensusFinite23
import D4Bound.CensusFinite24
import D4Bound.CensusFinite25
import D4Bound.CensusFinite26
import Mathlib.Tactic.IntervalCases

namespace D4Bound.CensusArithmetic
theorem all_counts_checked (N : ℕ) (hN : N ≤ 26) : allAt N test = true := by
  interval_cases N
  · exact census_N0
  · exact census_N1
  · exact census_N2
  · exact census_N3
  · exact census_N4
  · exact census_N5
  · exact census_N6
  · exact census_N7
  · exact census_N8
  · exact census_N9
  · exact census_N10
  · exact census_N11
  · exact census_N12
  · exact census_N13
  · exact census_N14
  · exact census_N15
  · exact census_N16
  · exact census_N17
  · exact census_N18
  · exact census_N19
  · exact census_N20
  · exact census_N21
  · exact census_N22
  · exact census_N23
  · exact census_N24
  · exact census_N25
  · exact census_N26

/-- Every allowed count vector has at least its rounded ledger floor under the
explicit arithmetic energy formula. Concrete-kernel energy domination is separate. -/
theorem numeric_floor {v : Counts} (hv : Valid v) {g : ℕ × ℕ × ℚ}
    (hg : g ∈ groups) (hN : g.1 = v.n4) (hj : g.2.1 = first v) :
    g.2.2 ≤ lower v := by
  have hb : v.n4 ≤ 26 := hv.2.2.2.2.2.2.1
  exact test_sound (allAt_sound (all_counts_checked v.n4 hb) v hv rfl) hg hN hj

end D4Bound.CensusArithmetic
