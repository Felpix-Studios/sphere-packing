import D4Bound.CensusCheck
import Mathlib.Tactic.IntervalCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
/-! Generated bounded-memory census blocks; each is checked by Lean. -/
namespace D4Bound.CensusArithmetic
private theorem chunk_22_0_0_0 :
    atPairChunk 22 0 0 0 test = true := by decide +kernel
private theorem chunk_22_0_0_1 :
    atPairChunk 22 0 0 1 test = true := by decide +kernel
private theorem chunk_22_0_0_2 :
    atPairChunk 22 0 0 2 test = true := by decide +kernel
private theorem chunk_22_0_0_3 :
    atPairChunk 22 0 0 3 test = true := by decide +kernel
theorem pair_22_0_0 : atPair 22 0 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_0_0_0
  · exact chunk_22_0_0_1
  · exact chunk_22_0_0_2
  · exact chunk_22_0_0_3
private theorem chunk_22_1_0_0 :
    atPairChunk 22 1 0 0 test = true := by decide +kernel
private theorem chunk_22_1_0_1 :
    atPairChunk 22 1 0 1 test = true := by decide +kernel
private theorem chunk_22_1_0_2 :
    atPairChunk 22 1 0 2 test = true := by decide +kernel
private theorem chunk_22_1_0_3 :
    atPairChunk 22 1 0 3 test = true := by decide +kernel
theorem pair_22_1_0 : atPair 22 1 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_1_0_0
  · exact chunk_22_1_0_1
  · exact chunk_22_1_0_2
  · exact chunk_22_1_0_3
private theorem chunk_22_1_1_0 :
    atPairChunk 22 1 1 0 test = true := by decide +kernel
private theorem chunk_22_1_1_1 :
    atPairChunk 22 1 1 1 test = true := by decide +kernel
private theorem chunk_22_1_1_2 :
    atPairChunk 22 1 1 2 test = true := by decide +kernel
private theorem chunk_22_1_1_3 :
    atPairChunk 22 1 1 3 test = true := by decide +kernel
theorem pair_22_1_1 : atPair 22 1 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_1_1_0
  · exact chunk_22_1_1_1
  · exact chunk_22_1_1_2
  · exact chunk_22_1_1_3
private theorem chunk_22_2_0_0 :
    atPairChunk 22 2 0 0 test = true := by decide +kernel
private theorem chunk_22_2_0_1 :
    atPairChunk 22 2 0 1 test = true := by decide +kernel
private theorem chunk_22_2_0_2 :
    atPairChunk 22 2 0 2 test = true := by decide +kernel
private theorem chunk_22_2_0_3 :
    atPairChunk 22 2 0 3 test = true := by decide +kernel
theorem pair_22_2_0 : atPair 22 2 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_2_0_0
  · exact chunk_22_2_0_1
  · exact chunk_22_2_0_2
  · exact chunk_22_2_0_3
private theorem chunk_22_2_1_0 :
    atPairChunk 22 2 1 0 test = true := by decide +kernel
private theorem chunk_22_2_1_1 :
    atPairChunk 22 2 1 1 test = true := by decide +kernel
private theorem chunk_22_2_1_2 :
    atPairChunk 22 2 1 2 test = true := by decide +kernel
private theorem chunk_22_2_1_3 :
    atPairChunk 22 2 1 3 test = true := by decide +kernel
theorem pair_22_2_1 : atPair 22 2 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_2_1_0
  · exact chunk_22_2_1_1
  · exact chunk_22_2_1_2
  · exact chunk_22_2_1_3
private theorem chunk_22_2_2_0 :
    atPairChunk 22 2 2 0 test = true := by decide +kernel
private theorem chunk_22_2_2_1 :
    atPairChunk 22 2 2 1 test = true := by decide +kernel
private theorem chunk_22_2_2_2 :
    atPairChunk 22 2 2 2 test = true := by decide +kernel
private theorem chunk_22_2_2_3 :
    atPairChunk 22 2 2 3 test = true := by decide +kernel
theorem pair_22_2_2 : atPair 22 2 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_2_2_0
  · exact chunk_22_2_2_1
  · exact chunk_22_2_2_2
  · exact chunk_22_2_2_3
private theorem chunk_22_3_0_0 :
    atPairChunk 22 3 0 0 test = true := by decide +kernel
private theorem chunk_22_3_0_1 :
    atPairChunk 22 3 0 1 test = true := by decide +kernel
private theorem chunk_22_3_0_2 :
    atPairChunk 22 3 0 2 test = true := by decide +kernel
private theorem chunk_22_3_0_3 :
    atPairChunk 22 3 0 3 test = true := by decide +kernel
theorem pair_22_3_0 : atPair 22 3 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_3_0_0
  · exact chunk_22_3_0_1
  · exact chunk_22_3_0_2
  · exact chunk_22_3_0_3
private theorem chunk_22_3_1_0 :
    atPairChunk 22 3 1 0 test = true := by decide +kernel
private theorem chunk_22_3_1_1 :
    atPairChunk 22 3 1 1 test = true := by decide +kernel
private theorem chunk_22_3_1_2 :
    atPairChunk 22 3 1 2 test = true := by decide +kernel
private theorem chunk_22_3_1_3 :
    atPairChunk 22 3 1 3 test = true := by decide +kernel
theorem pair_22_3_1 : atPair 22 3 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_3_1_0
  · exact chunk_22_3_1_1
  · exact chunk_22_3_1_2
  · exact chunk_22_3_1_3
private theorem chunk_22_3_2_0 :
    atPairChunk 22 3 2 0 test = true := by decide +kernel
private theorem chunk_22_3_2_1 :
    atPairChunk 22 3 2 1 test = true := by decide +kernel
private theorem chunk_22_3_2_2 :
    atPairChunk 22 3 2 2 test = true := by decide +kernel
private theorem chunk_22_3_2_3 :
    atPairChunk 22 3 2 3 test = true := by decide +kernel
theorem pair_22_3_2 : atPair 22 3 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_3_2_0
  · exact chunk_22_3_2_1
  · exact chunk_22_3_2_2
  · exact chunk_22_3_2_3
private theorem chunk_22_3_3_0 :
    atPairChunk 22 3 3 0 test = true := by decide +kernel
private theorem chunk_22_3_3_1 :
    atPairChunk 22 3 3 1 test = true := by decide +kernel
private theorem chunk_22_3_3_2 :
    atPairChunk 22 3 3 2 test = true := by decide +kernel
private theorem chunk_22_3_3_3 :
    atPairChunk 22 3 3 3 test = true := by decide +kernel
theorem pair_22_3_3 : atPair 22 3 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_3_3_0
  · exact chunk_22_3_3_1
  · exact chunk_22_3_3_2
  · exact chunk_22_3_3_3
private theorem chunk_22_4_0_0 :
    atPairChunk 22 4 0 0 test = true := by decide +kernel
private theorem chunk_22_4_0_1 :
    atPairChunk 22 4 0 1 test = true := by decide +kernel
private theorem chunk_22_4_0_2 :
    atPairChunk 22 4 0 2 test = true := by decide +kernel
private theorem chunk_22_4_0_3 :
    atPairChunk 22 4 0 3 test = true := by decide +kernel
theorem pair_22_4_0 : atPair 22 4 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_4_0_0
  · exact chunk_22_4_0_1
  · exact chunk_22_4_0_2
  · exact chunk_22_4_0_3
private theorem chunk_22_4_1_0 :
    atPairChunk 22 4 1 0 test = true := by decide +kernel
private theorem chunk_22_4_1_1 :
    atPairChunk 22 4 1 1 test = true := by decide +kernel
private theorem chunk_22_4_1_2 :
    atPairChunk 22 4 1 2 test = true := by decide +kernel
private theorem chunk_22_4_1_3 :
    atPairChunk 22 4 1 3 test = true := by decide +kernel
theorem pair_22_4_1 : atPair 22 4 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_4_1_0
  · exact chunk_22_4_1_1
  · exact chunk_22_4_1_2
  · exact chunk_22_4_1_3
private theorem chunk_22_4_2_0 :
    atPairChunk 22 4 2 0 test = true := by decide +kernel
private theorem chunk_22_4_2_1 :
    atPairChunk 22 4 2 1 test = true := by decide +kernel
private theorem chunk_22_4_2_2 :
    atPairChunk 22 4 2 2 test = true := by decide +kernel
private theorem chunk_22_4_2_3 :
    atPairChunk 22 4 2 3 test = true := by decide +kernel
theorem pair_22_4_2 : atPair 22 4 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_4_2_0
  · exact chunk_22_4_2_1
  · exact chunk_22_4_2_2
  · exact chunk_22_4_2_3
private theorem chunk_22_4_3_0 :
    atPairChunk 22 4 3 0 test = true := by decide +kernel
private theorem chunk_22_4_3_1 :
    atPairChunk 22 4 3 1 test = true := by decide +kernel
private theorem chunk_22_4_3_2 :
    atPairChunk 22 4 3 2 test = true := by decide +kernel
private theorem chunk_22_4_3_3 :
    atPairChunk 22 4 3 3 test = true := by decide +kernel
theorem pair_22_4_3 : atPair 22 4 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_4_3_0
  · exact chunk_22_4_3_1
  · exact chunk_22_4_3_2
  · exact chunk_22_4_3_3
private theorem chunk_22_4_4_0 :
    atPairChunk 22 4 4 0 test = true := by decide +kernel
private theorem chunk_22_4_4_1 :
    atPairChunk 22 4 4 1 test = true := by decide +kernel
private theorem chunk_22_4_4_2 :
    atPairChunk 22 4 4 2 test = true := by decide +kernel
private theorem chunk_22_4_4_3 :
    atPairChunk 22 4 4 3 test = true := by decide +kernel
theorem pair_22_4_4 : atPair 22 4 4 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_4_4_0
  · exact chunk_22_4_4_1
  · exact chunk_22_4_4_2
  · exact chunk_22_4_4_3
private theorem chunk_22_5_0_0 :
    atPairChunk 22 5 0 0 test = true := by decide +kernel
private theorem chunk_22_5_0_1 :
    atPairChunk 22 5 0 1 test = true := by decide +kernel
private theorem chunk_22_5_0_2 :
    atPairChunk 22 5 0 2 test = true := by decide +kernel
private theorem chunk_22_5_0_3 :
    atPairChunk 22 5 0 3 test = true := by decide +kernel
theorem pair_22_5_0 : atPair 22 5 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_5_0_0
  · exact chunk_22_5_0_1
  · exact chunk_22_5_0_2
  · exact chunk_22_5_0_3
private theorem chunk_22_5_1_0 :
    atPairChunk 22 5 1 0 test = true := by decide +kernel
private theorem chunk_22_5_1_1 :
    atPairChunk 22 5 1 1 test = true := by decide +kernel
private theorem chunk_22_5_1_2 :
    atPairChunk 22 5 1 2 test = true := by decide +kernel
private theorem chunk_22_5_1_3 :
    atPairChunk 22 5 1 3 test = true := by decide +kernel
theorem pair_22_5_1 : atPair 22 5 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_5_1_0
  · exact chunk_22_5_1_1
  · exact chunk_22_5_1_2
  · exact chunk_22_5_1_3
private theorem chunk_22_5_2_0 :
    atPairChunk 22 5 2 0 test = true := by decide +kernel
private theorem chunk_22_5_2_1 :
    atPairChunk 22 5 2 1 test = true := by decide +kernel
private theorem chunk_22_5_2_2 :
    atPairChunk 22 5 2 2 test = true := by decide +kernel
private theorem chunk_22_5_2_3 :
    atPairChunk 22 5 2 3 test = true := by decide +kernel
theorem pair_22_5_2 : atPair 22 5 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_5_2_0
  · exact chunk_22_5_2_1
  · exact chunk_22_5_2_2
  · exact chunk_22_5_2_3
private theorem chunk_22_5_3_0 :
    atPairChunk 22 5 3 0 test = true := by decide +kernel
private theorem chunk_22_5_3_1 :
    atPairChunk 22 5 3 1 test = true := by decide +kernel
private theorem chunk_22_5_3_2 :
    atPairChunk 22 5 3 2 test = true := by decide +kernel
private theorem chunk_22_5_3_3 :
    atPairChunk 22 5 3 3 test = true := by decide +kernel
theorem pair_22_5_3 : atPair 22 5 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_5_3_0
  · exact chunk_22_5_3_1
  · exact chunk_22_5_3_2
  · exact chunk_22_5_3_3
private theorem chunk_22_5_4_0 :
    atPairChunk 22 5 4 0 test = true := by decide +kernel
private theorem chunk_22_5_4_1 :
    atPairChunk 22 5 4 1 test = true := by decide +kernel
private theorem chunk_22_5_4_2 :
    atPairChunk 22 5 4 2 test = true := by decide +kernel
private theorem chunk_22_5_4_3 :
    atPairChunk 22 5 4 3 test = true := by decide +kernel
theorem pair_22_5_4 : atPair 22 5 4 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_5_4_0
  · exact chunk_22_5_4_1
  · exact chunk_22_5_4_2
  · exact chunk_22_5_4_3
private theorem chunk_22_5_5_0 :
    atPairChunk 22 5 5 0 test = true := by decide +kernel
private theorem chunk_22_5_5_1 :
    atPairChunk 22 5 5 1 test = true := by decide +kernel
private theorem chunk_22_5_5_2 :
    atPairChunk 22 5 5 2 test = true := by decide +kernel
private theorem chunk_22_5_5_3 :
    atPairChunk 22 5 5 3 test = true := by decide +kernel
theorem pair_22_5_5 : atPair 22 5 5 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_5_5_0
  · exact chunk_22_5_5_1
  · exact chunk_22_5_5_2
  · exact chunk_22_5_5_3
private theorem chunk_22_6_0_0 :
    atPairChunk 22 6 0 0 test = true := by decide +kernel
private theorem chunk_22_6_0_1 :
    atPairChunk 22 6 0 1 test = true := by decide +kernel
private theorem chunk_22_6_0_2 :
    atPairChunk 22 6 0 2 test = true := by decide +kernel
private theorem chunk_22_6_0_3 :
    atPairChunk 22 6 0 3 test = true := by decide +kernel
theorem pair_22_6_0 : atPair 22 6 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_0_0
  · exact chunk_22_6_0_1
  · exact chunk_22_6_0_2
  · exact chunk_22_6_0_3
private theorem chunk_22_6_1_0 :
    atPairChunk 22 6 1 0 test = true := by decide +kernel
private theorem chunk_22_6_1_1 :
    atPairChunk 22 6 1 1 test = true := by decide +kernel
private theorem chunk_22_6_1_2 :
    atPairChunk 22 6 1 2 test = true := by decide +kernel
private theorem chunk_22_6_1_3 :
    atPairChunk 22 6 1 3 test = true := by decide +kernel
theorem pair_22_6_1 : atPair 22 6 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_1_0
  · exact chunk_22_6_1_1
  · exact chunk_22_6_1_2
  · exact chunk_22_6_1_3
private theorem chunk_22_6_2_0 :
    atPairChunk 22 6 2 0 test = true := by decide +kernel
private theorem chunk_22_6_2_1 :
    atPairChunk 22 6 2 1 test = true := by decide +kernel
private theorem chunk_22_6_2_2 :
    atPairChunk 22 6 2 2 test = true := by decide +kernel
private theorem chunk_22_6_2_3 :
    atPairChunk 22 6 2 3 test = true := by decide +kernel
theorem pair_22_6_2 : atPair 22 6 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_2_0
  · exact chunk_22_6_2_1
  · exact chunk_22_6_2_2
  · exact chunk_22_6_2_3
private theorem chunk_22_6_3_0 :
    atPairChunk 22 6 3 0 test = true := by decide +kernel
private theorem chunk_22_6_3_1 :
    atPairChunk 22 6 3 1 test = true := by decide +kernel
private theorem chunk_22_6_3_2 :
    atPairChunk 22 6 3 2 test = true := by decide +kernel
private theorem chunk_22_6_3_3 :
    atPairChunk 22 6 3 3 test = true := by decide +kernel
theorem pair_22_6_3 : atPair 22 6 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_3_0
  · exact chunk_22_6_3_1
  · exact chunk_22_6_3_2
  · exact chunk_22_6_3_3
private theorem chunk_22_6_4_0 :
    atPairChunk 22 6 4 0 test = true := by decide +kernel
private theorem chunk_22_6_4_1 :
    atPairChunk 22 6 4 1 test = true := by decide +kernel
private theorem chunk_22_6_4_2 :
    atPairChunk 22 6 4 2 test = true := by decide +kernel
private theorem chunk_22_6_4_3 :
    atPairChunk 22 6 4 3 test = true := by decide +kernel
theorem pair_22_6_4 : atPair 22 6 4 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_4_0
  · exact chunk_22_6_4_1
  · exact chunk_22_6_4_2
  · exact chunk_22_6_4_3
private theorem chunk_22_6_5_0 :
    atPairChunk 22 6 5 0 test = true := by decide +kernel
private theorem chunk_22_6_5_1 :
    atPairChunk 22 6 5 1 test = true := by decide +kernel
private theorem chunk_22_6_5_2 :
    atPairChunk 22 6 5 2 test = true := by decide +kernel
private theorem chunk_22_6_5_3 :
    atPairChunk 22 6 5 3 test = true := by decide +kernel
theorem pair_22_6_5 : atPair 22 6 5 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_5_0
  · exact chunk_22_6_5_1
  · exact chunk_22_6_5_2
  · exact chunk_22_6_5_3
private theorem chunk_22_6_6_0 :
    atPairChunk 22 6 6 0 test = true := by decide +kernel
private theorem chunk_22_6_6_1 :
    atPairChunk 22 6 6 1 test = true := by decide +kernel
private theorem chunk_22_6_6_2 :
    atPairChunk 22 6 6 2 test = true := by decide +kernel
private theorem chunk_22_6_6_3 :
    atPairChunk 22 6 6 3 test = true := by decide +kernel
theorem pair_22_6_6 : atPair 22 6 6 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_6_6_0
  · exact chunk_22_6_6_1
  · exact chunk_22_6_6_2
  · exact chunk_22_6_6_3
private theorem chunk_22_7_0_0 :
    atPairChunk 22 7 0 0 test = true := by decide +kernel
private theorem chunk_22_7_0_1 :
    atPairChunk 22 7 0 1 test = true := by decide +kernel
private theorem chunk_22_7_0_2 :
    atPairChunk 22 7 0 2 test = true := by decide +kernel
private theorem chunk_22_7_0_3 :
    atPairChunk 22 7 0 3 test = true := by decide +kernel
theorem pair_22_7_0 : atPair 22 7 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_0_0
  · exact chunk_22_7_0_1
  · exact chunk_22_7_0_2
  · exact chunk_22_7_0_3
private theorem chunk_22_7_1_0 :
    atPairChunk 22 7 1 0 test = true := by decide +kernel
private theorem chunk_22_7_1_1 :
    atPairChunk 22 7 1 1 test = true := by decide +kernel
private theorem chunk_22_7_1_2 :
    atPairChunk 22 7 1 2 test = true := by decide +kernel
private theorem chunk_22_7_1_3 :
    atPairChunk 22 7 1 3 test = true := by decide +kernel
theorem pair_22_7_1 : atPair 22 7 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_1_0
  · exact chunk_22_7_1_1
  · exact chunk_22_7_1_2
  · exact chunk_22_7_1_3
private theorem chunk_22_7_2_0 :
    atPairChunk 22 7 2 0 test = true := by decide +kernel
private theorem chunk_22_7_2_1 :
    atPairChunk 22 7 2 1 test = true := by decide +kernel
private theorem chunk_22_7_2_2 :
    atPairChunk 22 7 2 2 test = true := by decide +kernel
private theorem chunk_22_7_2_3 :
    atPairChunk 22 7 2 3 test = true := by decide +kernel
theorem pair_22_7_2 : atPair 22 7 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_2_0
  · exact chunk_22_7_2_1
  · exact chunk_22_7_2_2
  · exact chunk_22_7_2_3
private theorem chunk_22_7_3_0 :
    atPairChunk 22 7 3 0 test = true := by decide +kernel
private theorem chunk_22_7_3_1 :
    atPairChunk 22 7 3 1 test = true := by decide +kernel
private theorem chunk_22_7_3_2 :
    atPairChunk 22 7 3 2 test = true := by decide +kernel
private theorem chunk_22_7_3_3 :
    atPairChunk 22 7 3 3 test = true := by decide +kernel
theorem pair_22_7_3 : atPair 22 7 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_3_0
  · exact chunk_22_7_3_1
  · exact chunk_22_7_3_2
  · exact chunk_22_7_3_3
private theorem chunk_22_7_4_0 :
    atPairChunk 22 7 4 0 test = true := by decide +kernel
private theorem chunk_22_7_4_1 :
    atPairChunk 22 7 4 1 test = true := by decide +kernel
private theorem chunk_22_7_4_2 :
    atPairChunk 22 7 4 2 test = true := by decide +kernel
private theorem chunk_22_7_4_3 :
    atPairChunk 22 7 4 3 test = true := by decide +kernel
theorem pair_22_7_4 : atPair 22 7 4 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_4_0
  · exact chunk_22_7_4_1
  · exact chunk_22_7_4_2
  · exact chunk_22_7_4_3
private theorem chunk_22_7_5_0 :
    atPairChunk 22 7 5 0 test = true := by decide +kernel
private theorem chunk_22_7_5_1 :
    atPairChunk 22 7 5 1 test = true := by decide +kernel
private theorem chunk_22_7_5_2 :
    atPairChunk 22 7 5 2 test = true := by decide +kernel
private theorem chunk_22_7_5_3 :
    atPairChunk 22 7 5 3 test = true := by decide +kernel
theorem pair_22_7_5 : atPair 22 7 5 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_5_0
  · exact chunk_22_7_5_1
  · exact chunk_22_7_5_2
  · exact chunk_22_7_5_3
private theorem chunk_22_7_6_0 :
    atPairChunk 22 7 6 0 test = true := by decide +kernel
private theorem chunk_22_7_6_1 :
    atPairChunk 22 7 6 1 test = true := by decide +kernel
private theorem chunk_22_7_6_2 :
    atPairChunk 22 7 6 2 test = true := by decide +kernel
private theorem chunk_22_7_6_3 :
    atPairChunk 22 7 6 3 test = true := by decide +kernel
theorem pair_22_7_6 : atPair 22 7 6 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_6_0
  · exact chunk_22_7_6_1
  · exact chunk_22_7_6_2
  · exact chunk_22_7_6_3
private theorem chunk_22_7_7_0 :
    atPairChunk 22 7 7 0 test = true := by decide +kernel
private theorem chunk_22_7_7_1 :
    atPairChunk 22 7 7 1 test = true := by decide +kernel
private theorem chunk_22_7_7_2 :
    atPairChunk 22 7 7 2 test = true := by decide +kernel
private theorem chunk_22_7_7_3 :
    atPairChunk 22 7 7 3 test = true := by decide +kernel
theorem pair_22_7_7 : atPair 22 7 7 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_22_7_7_0
  · exact chunk_22_7_7_1
  · exact chunk_22_7_7_2
  · exact chunk_22_7_7_3
end D4Bound.CensusArithmetic
