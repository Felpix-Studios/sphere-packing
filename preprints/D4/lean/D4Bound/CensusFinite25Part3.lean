import D4Bound.CensusCheck
import Mathlib.Tactic.IntervalCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
/-! Generated bounded-memory census blocks; each is checked by Lean. -/
namespace D4Bound.CensusArithmetic
private theorem chunk_25_24_0_0 :
    atPairChunk 25 24 0 0 test = true := by decide +kernel
private theorem chunk_25_24_0_1 :
    atPairChunk 25 24 0 1 test = true := by decide +kernel
private theorem chunk_25_24_0_2 :
    atPairChunk 25 24 0 2 test = true := by decide +kernel
private theorem chunk_25_24_0_3 :
    atPairChunk 25 24 0 3 test = true := by decide +kernel
theorem pair_25_24_0 : atPair 25 24 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_0_0
  · exact chunk_25_24_0_1
  · exact chunk_25_24_0_2
  · exact chunk_25_24_0_3
private theorem chunk_25_24_1_0 :
    atPairChunk 25 24 1 0 test = true := by decide +kernel
private theorem chunk_25_24_1_1 :
    atPairChunk 25 24 1 1 test = true := by decide +kernel
private theorem chunk_25_24_1_2 :
    atPairChunk 25 24 1 2 test = true := by decide +kernel
private theorem chunk_25_24_1_3 :
    atPairChunk 25 24 1 3 test = true := by decide +kernel
theorem pair_25_24_1 : atPair 25 24 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_1_0
  · exact chunk_25_24_1_1
  · exact chunk_25_24_1_2
  · exact chunk_25_24_1_3
private theorem chunk_25_24_2_0 :
    atPairChunk 25 24 2 0 test = true := by decide +kernel
private theorem chunk_25_24_2_1 :
    atPairChunk 25 24 2 1 test = true := by decide +kernel
private theorem chunk_25_24_2_2 :
    atPairChunk 25 24 2 2 test = true := by decide +kernel
private theorem chunk_25_24_2_3 :
    atPairChunk 25 24 2 3 test = true := by decide +kernel
theorem pair_25_24_2 : atPair 25 24 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_2_0
  · exact chunk_25_24_2_1
  · exact chunk_25_24_2_2
  · exact chunk_25_24_2_3
private theorem chunk_25_24_3_0 :
    atPairChunk 25 24 3 0 test = true := by decide +kernel
private theorem chunk_25_24_3_1 :
    atPairChunk 25 24 3 1 test = true := by decide +kernel
private theorem chunk_25_24_3_2 :
    atPairChunk 25 24 3 2 test = true := by decide +kernel
private theorem chunk_25_24_3_3 :
    atPairChunk 25 24 3 3 test = true := by decide +kernel
theorem pair_25_24_3 : atPair 25 24 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_3_0
  · exact chunk_25_24_3_1
  · exact chunk_25_24_3_2
  · exact chunk_25_24_3_3
private theorem chunk_25_24_4_0 :
    atPairChunk 25 24 4 0 test = true := by decide +kernel
private theorem chunk_25_24_4_1 :
    atPairChunk 25 24 4 1 test = true := by decide +kernel
private theorem chunk_25_24_4_2 :
    atPairChunk 25 24 4 2 test = true := by decide +kernel
private theorem chunk_25_24_4_3 :
    atPairChunk 25 24 4 3 test = true := by decide +kernel
theorem pair_25_24_4 : atPair 25 24 4 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_4_0
  · exact chunk_25_24_4_1
  · exact chunk_25_24_4_2
  · exact chunk_25_24_4_3
private theorem chunk_25_24_5_0 :
    atPairChunk 25 24 5 0 test = true := by decide +kernel
private theorem chunk_25_24_5_1 :
    atPairChunk 25 24 5 1 test = true := by decide +kernel
private theorem chunk_25_24_5_2 :
    atPairChunk 25 24 5 2 test = true := by decide +kernel
private theorem chunk_25_24_5_3 :
    atPairChunk 25 24 5 3 test = true := by decide +kernel
theorem pair_25_24_5 : atPair 25 24 5 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_5_0
  · exact chunk_25_24_5_1
  · exact chunk_25_24_5_2
  · exact chunk_25_24_5_3
private theorem chunk_25_24_6_0 :
    atPairChunk 25 24 6 0 test = true := by decide +kernel
private theorem chunk_25_24_6_1 :
    atPairChunk 25 24 6 1 test = true := by decide +kernel
private theorem chunk_25_24_6_2 :
    atPairChunk 25 24 6 2 test = true := by decide +kernel
private theorem chunk_25_24_6_3 :
    atPairChunk 25 24 6 3 test = true := by decide +kernel
theorem pair_25_24_6 : atPair 25 24 6 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_6_0
  · exact chunk_25_24_6_1
  · exact chunk_25_24_6_2
  · exact chunk_25_24_6_3
private theorem chunk_25_24_7_0 :
    atPairChunk 25 24 7 0 test = true := by decide +kernel
private theorem chunk_25_24_7_1 :
    atPairChunk 25 24 7 1 test = true := by decide +kernel
private theorem chunk_25_24_7_2 :
    atPairChunk 25 24 7 2 test = true := by decide +kernel
private theorem chunk_25_24_7_3 :
    atPairChunk 25 24 7 3 test = true := by decide +kernel
theorem pair_25_24_7 : atPair 25 24 7 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_7_0
  · exact chunk_25_24_7_1
  · exact chunk_25_24_7_2
  · exact chunk_25_24_7_3
private theorem chunk_25_24_8_0 :
    atPairChunk 25 24 8 0 test = true := by decide +kernel
private theorem chunk_25_24_8_1 :
    atPairChunk 25 24 8 1 test = true := by decide +kernel
private theorem chunk_25_24_8_2 :
    atPairChunk 25 24 8 2 test = true := by decide +kernel
private theorem chunk_25_24_8_3 :
    atPairChunk 25 24 8 3 test = true := by decide +kernel
theorem pair_25_24_8 : atPair 25 24 8 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_8_0
  · exact chunk_25_24_8_1
  · exact chunk_25_24_8_2
  · exact chunk_25_24_8_3
private theorem chunk_25_24_9_0 :
    atPairChunk 25 24 9 0 test = true := by decide +kernel
private theorem chunk_25_24_9_1 :
    atPairChunk 25 24 9 1 test = true := by decide +kernel
private theorem chunk_25_24_9_2 :
    atPairChunk 25 24 9 2 test = true := by decide +kernel
private theorem chunk_25_24_9_3 :
    atPairChunk 25 24 9 3 test = true := by decide +kernel
theorem pair_25_24_9 : atPair 25 24 9 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_9_0
  · exact chunk_25_24_9_1
  · exact chunk_25_24_9_2
  · exact chunk_25_24_9_3
private theorem chunk_25_24_10_0 :
    atPairChunk 25 24 10 0 test = true := by decide +kernel
private theorem chunk_25_24_10_1 :
    atPairChunk 25 24 10 1 test = true := by decide +kernel
private theorem chunk_25_24_10_2 :
    atPairChunk 25 24 10 2 test = true := by decide +kernel
private theorem chunk_25_24_10_3 :
    atPairChunk 25 24 10 3 test = true := by decide +kernel
theorem pair_25_24_10 : atPair 25 24 10 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_10_0
  · exact chunk_25_24_10_1
  · exact chunk_25_24_10_2
  · exact chunk_25_24_10_3
private theorem chunk_25_24_11_0 :
    atPairChunk 25 24 11 0 test = true := by decide +kernel
private theorem chunk_25_24_11_1 :
    atPairChunk 25 24 11 1 test = true := by decide +kernel
private theorem chunk_25_24_11_2 :
    atPairChunk 25 24 11 2 test = true := by decide +kernel
private theorem chunk_25_24_11_3 :
    atPairChunk 25 24 11 3 test = true := by decide +kernel
theorem pair_25_24_11 : atPair 25 24 11 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_11_0
  · exact chunk_25_24_11_1
  · exact chunk_25_24_11_2
  · exact chunk_25_24_11_3
private theorem chunk_25_24_12_0 :
    atPairChunk 25 24 12 0 test = true := by decide +kernel
private theorem chunk_25_24_12_1 :
    atPairChunk 25 24 12 1 test = true := by decide +kernel
private theorem chunk_25_24_12_2 :
    atPairChunk 25 24 12 2 test = true := by decide +kernel
private theorem chunk_25_24_12_3 :
    atPairChunk 25 24 12 3 test = true := by decide +kernel
theorem pair_25_24_12 : atPair 25 24 12 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_12_0
  · exact chunk_25_24_12_1
  · exact chunk_25_24_12_2
  · exact chunk_25_24_12_3
private theorem chunk_25_24_13_0 :
    atPairChunk 25 24 13 0 test = true := by decide +kernel
private theorem chunk_25_24_13_1 :
    atPairChunk 25 24 13 1 test = true := by decide +kernel
private theorem chunk_25_24_13_2 :
    atPairChunk 25 24 13 2 test = true := by decide +kernel
private theorem chunk_25_24_13_3 :
    atPairChunk 25 24 13 3 test = true := by decide +kernel
theorem pair_25_24_13 : atPair 25 24 13 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_13_0
  · exact chunk_25_24_13_1
  · exact chunk_25_24_13_2
  · exact chunk_25_24_13_3
private theorem chunk_25_24_14_0 :
    atPairChunk 25 24 14 0 test = true := by decide +kernel
private theorem chunk_25_24_14_1 :
    atPairChunk 25 24 14 1 test = true := by decide +kernel
private theorem chunk_25_24_14_2 :
    atPairChunk 25 24 14 2 test = true := by decide +kernel
private theorem chunk_25_24_14_3 :
    atPairChunk 25 24 14 3 test = true := by decide +kernel
theorem pair_25_24_14 : atPair 25 24 14 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_14_0
  · exact chunk_25_24_14_1
  · exact chunk_25_24_14_2
  · exact chunk_25_24_14_3
private theorem chunk_25_24_15_0 :
    atPairChunk 25 24 15 0 test = true := by decide +kernel
private theorem chunk_25_24_15_1 :
    atPairChunk 25 24 15 1 test = true := by decide +kernel
private theorem chunk_25_24_15_2 :
    atPairChunk 25 24 15 2 test = true := by decide +kernel
private theorem chunk_25_24_15_3 :
    atPairChunk 25 24 15 3 test = true := by decide +kernel
theorem pair_25_24_15 : atPair 25 24 15 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_15_0
  · exact chunk_25_24_15_1
  · exact chunk_25_24_15_2
  · exact chunk_25_24_15_3
private theorem chunk_25_24_16_0 :
    atPairChunk 25 24 16 0 test = true := by decide +kernel
private theorem chunk_25_24_16_1 :
    atPairChunk 25 24 16 1 test = true := by decide +kernel
private theorem chunk_25_24_16_2 :
    atPairChunk 25 24 16 2 test = true := by decide +kernel
private theorem chunk_25_24_16_3 :
    atPairChunk 25 24 16 3 test = true := by decide +kernel
theorem pair_25_24_16 : atPair 25 24 16 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_16_0
  · exact chunk_25_24_16_1
  · exact chunk_25_24_16_2
  · exact chunk_25_24_16_3
private theorem chunk_25_24_17_0 :
    atPairChunk 25 24 17 0 test = true := by decide +kernel
private theorem chunk_25_24_17_1 :
    atPairChunk 25 24 17 1 test = true := by decide +kernel
private theorem chunk_25_24_17_2 :
    atPairChunk 25 24 17 2 test = true := by decide +kernel
private theorem chunk_25_24_17_3 :
    atPairChunk 25 24 17 3 test = true := by decide +kernel
theorem pair_25_24_17 : atPair 25 24 17 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_17_0
  · exact chunk_25_24_17_1
  · exact chunk_25_24_17_2
  · exact chunk_25_24_17_3
private theorem chunk_25_24_18_0 :
    atPairChunk 25 24 18 0 test = true := by decide +kernel
private theorem chunk_25_24_18_1 :
    atPairChunk 25 24 18 1 test = true := by decide +kernel
private theorem chunk_25_24_18_2 :
    atPairChunk 25 24 18 2 test = true := by decide +kernel
private theorem chunk_25_24_18_3 :
    atPairChunk 25 24 18 3 test = true := by decide +kernel
theorem pair_25_24_18 : atPair 25 24 18 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_18_0
  · exact chunk_25_24_18_1
  · exact chunk_25_24_18_2
  · exact chunk_25_24_18_3
private theorem chunk_25_24_19_0 :
    atPairChunk 25 24 19 0 test = true := by decide +kernel
private theorem chunk_25_24_19_1 :
    atPairChunk 25 24 19 1 test = true := by decide +kernel
private theorem chunk_25_24_19_2 :
    atPairChunk 25 24 19 2 test = true := by decide +kernel
private theorem chunk_25_24_19_3 :
    atPairChunk 25 24 19 3 test = true := by decide +kernel
theorem pair_25_24_19 : atPair 25 24 19 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_19_0
  · exact chunk_25_24_19_1
  · exact chunk_25_24_19_2
  · exact chunk_25_24_19_3
private theorem chunk_25_24_20_0 :
    atPairChunk 25 24 20 0 test = true := by decide +kernel
private theorem chunk_25_24_20_1 :
    atPairChunk 25 24 20 1 test = true := by decide +kernel
private theorem chunk_25_24_20_2 :
    atPairChunk 25 24 20 2 test = true := by decide +kernel
private theorem chunk_25_24_20_3 :
    atPairChunk 25 24 20 3 test = true := by decide +kernel
theorem pair_25_24_20 : atPair 25 24 20 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_20_0
  · exact chunk_25_24_20_1
  · exact chunk_25_24_20_2
  · exact chunk_25_24_20_3
private theorem chunk_25_24_21_0 :
    atPairChunk 25 24 21 0 test = true := by decide +kernel
private theorem chunk_25_24_21_1 :
    atPairChunk 25 24 21 1 test = true := by decide +kernel
private theorem chunk_25_24_21_2 :
    atPairChunk 25 24 21 2 test = true := by decide +kernel
private theorem chunk_25_24_21_3 :
    atPairChunk 25 24 21 3 test = true := by decide +kernel
theorem pair_25_24_21 : atPair 25 24 21 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_21_0
  · exact chunk_25_24_21_1
  · exact chunk_25_24_21_2
  · exact chunk_25_24_21_3
private theorem chunk_25_24_22_0 :
    atPairChunk 25 24 22 0 test = true := by decide +kernel
private theorem chunk_25_24_22_1 :
    atPairChunk 25 24 22 1 test = true := by decide +kernel
private theorem chunk_25_24_22_2 :
    atPairChunk 25 24 22 2 test = true := by decide +kernel
private theorem chunk_25_24_22_3 :
    atPairChunk 25 24 22 3 test = true := by decide +kernel
theorem pair_25_24_22 : atPair 25 24 22 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_22_0
  · exact chunk_25_24_22_1
  · exact chunk_25_24_22_2
  · exact chunk_25_24_22_3
private theorem chunk_25_24_23_0 :
    atPairChunk 25 24 23 0 test = true := by decide +kernel
private theorem chunk_25_24_23_1 :
    atPairChunk 25 24 23 1 test = true := by decide +kernel
private theorem chunk_25_24_23_2 :
    atPairChunk 25 24 23 2 test = true := by decide +kernel
private theorem chunk_25_24_23_3 :
    atPairChunk 25 24 23 3 test = true := by decide +kernel
theorem pair_25_24_23 : atPair 25 24 23 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_23_0
  · exact chunk_25_24_23_1
  · exact chunk_25_24_23_2
  · exact chunk_25_24_23_3
private theorem chunk_25_24_24_0 :
    atPairChunk 25 24 24 0 test = true := by decide +kernel
private theorem chunk_25_24_24_1 :
    atPairChunk 25 24 24 1 test = true := by decide +kernel
private theorem chunk_25_24_24_2 :
    atPairChunk 25 24 24 2 test = true := by decide +kernel
private theorem chunk_25_24_24_3 :
    atPairChunk 25 24 24 3 test = true := by decide +kernel
theorem pair_25_24_24 : atPair 25 24 24 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_24_24_0
  · exact chunk_25_24_24_1
  · exact chunk_25_24_24_2
  · exact chunk_25_24_24_3
private theorem chunk_25_25_0_0 :
    atPairChunk 25 25 0 0 test = true := by decide +kernel
private theorem chunk_25_25_0_1 :
    atPairChunk 25 25 0 1 test = true := by decide +kernel
private theorem chunk_25_25_0_2 :
    atPairChunk 25 25 0 2 test = true := by decide +kernel
private theorem chunk_25_25_0_3 :
    atPairChunk 25 25 0 3 test = true := by decide +kernel
theorem pair_25_25_0 : atPair 25 25 0 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_0_0
  · exact chunk_25_25_0_1
  · exact chunk_25_25_0_2
  · exact chunk_25_25_0_3
private theorem chunk_25_25_1_0 :
    atPairChunk 25 25 1 0 test = true := by decide +kernel
private theorem chunk_25_25_1_1 :
    atPairChunk 25 25 1 1 test = true := by decide +kernel
private theorem chunk_25_25_1_2 :
    atPairChunk 25 25 1 2 test = true := by decide +kernel
private theorem chunk_25_25_1_3 :
    atPairChunk 25 25 1 3 test = true := by decide +kernel
theorem pair_25_25_1 : atPair 25 25 1 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_1_0
  · exact chunk_25_25_1_1
  · exact chunk_25_25_1_2
  · exact chunk_25_25_1_3
private theorem chunk_25_25_2_0 :
    atPairChunk 25 25 2 0 test = true := by decide +kernel
private theorem chunk_25_25_2_1 :
    atPairChunk 25 25 2 1 test = true := by decide +kernel
private theorem chunk_25_25_2_2 :
    atPairChunk 25 25 2 2 test = true := by decide +kernel
private theorem chunk_25_25_2_3 :
    atPairChunk 25 25 2 3 test = true := by decide +kernel
theorem pair_25_25_2 : atPair 25 25 2 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_2_0
  · exact chunk_25_25_2_1
  · exact chunk_25_25_2_2
  · exact chunk_25_25_2_3
private theorem chunk_25_25_3_0 :
    atPairChunk 25 25 3 0 test = true := by decide +kernel
private theorem chunk_25_25_3_1 :
    atPairChunk 25 25 3 1 test = true := by decide +kernel
private theorem chunk_25_25_3_2 :
    atPairChunk 25 25 3 2 test = true := by decide +kernel
private theorem chunk_25_25_3_3 :
    atPairChunk 25 25 3 3 test = true := by decide +kernel
theorem pair_25_25_3 : atPair 25 25 3 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_3_0
  · exact chunk_25_25_3_1
  · exact chunk_25_25_3_2
  · exact chunk_25_25_3_3
private theorem chunk_25_25_4_0 :
    atPairChunk 25 25 4 0 test = true := by decide +kernel
private theorem chunk_25_25_4_1 :
    atPairChunk 25 25 4 1 test = true := by decide +kernel
private theorem chunk_25_25_4_2 :
    atPairChunk 25 25 4 2 test = true := by decide +kernel
private theorem chunk_25_25_4_3 :
    atPairChunk 25 25 4 3 test = true := by decide +kernel
theorem pair_25_25_4 : atPair 25 25 4 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_4_0
  · exact chunk_25_25_4_1
  · exact chunk_25_25_4_2
  · exact chunk_25_25_4_3
private theorem chunk_25_25_5_0 :
    atPairChunk 25 25 5 0 test = true := by decide +kernel
private theorem chunk_25_25_5_1 :
    atPairChunk 25 25 5 1 test = true := by decide +kernel
private theorem chunk_25_25_5_2 :
    atPairChunk 25 25 5 2 test = true := by decide +kernel
private theorem chunk_25_25_5_3 :
    atPairChunk 25 25 5 3 test = true := by decide +kernel
theorem pair_25_25_5 : atPair 25 25 5 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_5_0
  · exact chunk_25_25_5_1
  · exact chunk_25_25_5_2
  · exact chunk_25_25_5_3
private theorem chunk_25_25_6_0 :
    atPairChunk 25 25 6 0 test = true := by decide +kernel
private theorem chunk_25_25_6_1 :
    atPairChunk 25 25 6 1 test = true := by decide +kernel
private theorem chunk_25_25_6_2 :
    atPairChunk 25 25 6 2 test = true := by decide +kernel
private theorem chunk_25_25_6_3 :
    atPairChunk 25 25 6 3 test = true := by decide +kernel
theorem pair_25_25_6 : atPair 25 25 6 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_6_0
  · exact chunk_25_25_6_1
  · exact chunk_25_25_6_2
  · exact chunk_25_25_6_3
private theorem chunk_25_25_7_0 :
    atPairChunk 25 25 7 0 test = true := by decide +kernel
private theorem chunk_25_25_7_1 :
    atPairChunk 25 25 7 1 test = true := by decide +kernel
private theorem chunk_25_25_7_2 :
    atPairChunk 25 25 7 2 test = true := by decide +kernel
private theorem chunk_25_25_7_3 :
    atPairChunk 25 25 7 3 test = true := by decide +kernel
theorem pair_25_25_7 : atPair 25 25 7 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_7_0
  · exact chunk_25_25_7_1
  · exact chunk_25_25_7_2
  · exact chunk_25_25_7_3
private theorem chunk_25_25_8_0 :
    atPairChunk 25 25 8 0 test = true := by decide +kernel
private theorem chunk_25_25_8_1 :
    atPairChunk 25 25 8 1 test = true := by decide +kernel
private theorem chunk_25_25_8_2 :
    atPairChunk 25 25 8 2 test = true := by decide +kernel
private theorem chunk_25_25_8_3 :
    atPairChunk 25 25 8 3 test = true := by decide +kernel
theorem pair_25_25_8 : atPair 25 25 8 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_8_0
  · exact chunk_25_25_8_1
  · exact chunk_25_25_8_2
  · exact chunk_25_25_8_3
private theorem chunk_25_25_9_0 :
    atPairChunk 25 25 9 0 test = true := by decide +kernel
private theorem chunk_25_25_9_1 :
    atPairChunk 25 25 9 1 test = true := by decide +kernel
private theorem chunk_25_25_9_2 :
    atPairChunk 25 25 9 2 test = true := by decide +kernel
private theorem chunk_25_25_9_3 :
    atPairChunk 25 25 9 3 test = true := by decide +kernel
theorem pair_25_25_9 : atPair 25 25 9 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_9_0
  · exact chunk_25_25_9_1
  · exact chunk_25_25_9_2
  · exact chunk_25_25_9_3
private theorem chunk_25_25_10_0 :
    atPairChunk 25 25 10 0 test = true := by decide +kernel
private theorem chunk_25_25_10_1 :
    atPairChunk 25 25 10 1 test = true := by decide +kernel
private theorem chunk_25_25_10_2 :
    atPairChunk 25 25 10 2 test = true := by decide +kernel
private theorem chunk_25_25_10_3 :
    atPairChunk 25 25 10 3 test = true := by decide +kernel
theorem pair_25_25_10 : atPair 25 25 10 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_10_0
  · exact chunk_25_25_10_1
  · exact chunk_25_25_10_2
  · exact chunk_25_25_10_3
private theorem chunk_25_25_11_0 :
    atPairChunk 25 25 11 0 test = true := by decide +kernel
private theorem chunk_25_25_11_1 :
    atPairChunk 25 25 11 1 test = true := by decide +kernel
private theorem chunk_25_25_11_2 :
    atPairChunk 25 25 11 2 test = true := by decide +kernel
private theorem chunk_25_25_11_3 :
    atPairChunk 25 25 11 3 test = true := by decide +kernel
theorem pair_25_25_11 : atPair 25 25 11 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_11_0
  · exact chunk_25_25_11_1
  · exact chunk_25_25_11_2
  · exact chunk_25_25_11_3
private theorem chunk_25_25_12_0 :
    atPairChunk 25 25 12 0 test = true := by decide +kernel
private theorem chunk_25_25_12_1 :
    atPairChunk 25 25 12 1 test = true := by decide +kernel
private theorem chunk_25_25_12_2 :
    atPairChunk 25 25 12 2 test = true := by decide +kernel
private theorem chunk_25_25_12_3 :
    atPairChunk 25 25 12 3 test = true := by decide +kernel
theorem pair_25_25_12 : atPair 25 25 12 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_12_0
  · exact chunk_25_25_12_1
  · exact chunk_25_25_12_2
  · exact chunk_25_25_12_3
private theorem chunk_25_25_13_0 :
    atPairChunk 25 25 13 0 test = true := by decide +kernel
private theorem chunk_25_25_13_1 :
    atPairChunk 25 25 13 1 test = true := by decide +kernel
private theorem chunk_25_25_13_2 :
    atPairChunk 25 25 13 2 test = true := by decide +kernel
private theorem chunk_25_25_13_3 :
    atPairChunk 25 25 13 3 test = true := by decide +kernel
theorem pair_25_25_13 : atPair 25 25 13 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_13_0
  · exact chunk_25_25_13_1
  · exact chunk_25_25_13_2
  · exact chunk_25_25_13_3
private theorem chunk_25_25_14_0 :
    atPairChunk 25 25 14 0 test = true := by decide +kernel
private theorem chunk_25_25_14_1 :
    atPairChunk 25 25 14 1 test = true := by decide +kernel
private theorem chunk_25_25_14_2 :
    atPairChunk 25 25 14 2 test = true := by decide +kernel
private theorem chunk_25_25_14_3 :
    atPairChunk 25 25 14 3 test = true := by decide +kernel
theorem pair_25_25_14 : atPair 25 25 14 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_14_0
  · exact chunk_25_25_14_1
  · exact chunk_25_25_14_2
  · exact chunk_25_25_14_3
private theorem chunk_25_25_15_0 :
    atPairChunk 25 25 15 0 test = true := by decide +kernel
private theorem chunk_25_25_15_1 :
    atPairChunk 25 25 15 1 test = true := by decide +kernel
private theorem chunk_25_25_15_2 :
    atPairChunk 25 25 15 2 test = true := by decide +kernel
private theorem chunk_25_25_15_3 :
    atPairChunk 25 25 15 3 test = true := by decide +kernel
theorem pair_25_25_15 : atPair 25 25 15 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_15_0
  · exact chunk_25_25_15_1
  · exact chunk_25_25_15_2
  · exact chunk_25_25_15_3
private theorem chunk_25_25_16_0 :
    atPairChunk 25 25 16 0 test = true := by decide +kernel
private theorem chunk_25_25_16_1 :
    atPairChunk 25 25 16 1 test = true := by decide +kernel
private theorem chunk_25_25_16_2 :
    atPairChunk 25 25 16 2 test = true := by decide +kernel
private theorem chunk_25_25_16_3 :
    atPairChunk 25 25 16 3 test = true := by decide +kernel
theorem pair_25_25_16 : atPair 25 25 16 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_16_0
  · exact chunk_25_25_16_1
  · exact chunk_25_25_16_2
  · exact chunk_25_25_16_3
private theorem chunk_25_25_17_0 :
    atPairChunk 25 25 17 0 test = true := by decide +kernel
private theorem chunk_25_25_17_1 :
    atPairChunk 25 25 17 1 test = true := by decide +kernel
private theorem chunk_25_25_17_2 :
    atPairChunk 25 25 17 2 test = true := by decide +kernel
private theorem chunk_25_25_17_3 :
    atPairChunk 25 25 17 3 test = true := by decide +kernel
theorem pair_25_25_17 : atPair 25 25 17 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_17_0
  · exact chunk_25_25_17_1
  · exact chunk_25_25_17_2
  · exact chunk_25_25_17_3
private theorem chunk_25_25_18_0 :
    atPairChunk 25 25 18 0 test = true := by decide +kernel
private theorem chunk_25_25_18_1 :
    atPairChunk 25 25 18 1 test = true := by decide +kernel
private theorem chunk_25_25_18_2 :
    atPairChunk 25 25 18 2 test = true := by decide +kernel
private theorem chunk_25_25_18_3 :
    atPairChunk 25 25 18 3 test = true := by decide +kernel
theorem pair_25_25_18 : atPair 25 25 18 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_18_0
  · exact chunk_25_25_18_1
  · exact chunk_25_25_18_2
  · exact chunk_25_25_18_3
private theorem chunk_25_25_19_0 :
    atPairChunk 25 25 19 0 test = true := by decide +kernel
private theorem chunk_25_25_19_1 :
    atPairChunk 25 25 19 1 test = true := by decide +kernel
private theorem chunk_25_25_19_2 :
    atPairChunk 25 25 19 2 test = true := by decide +kernel
private theorem chunk_25_25_19_3 :
    atPairChunk 25 25 19 3 test = true := by decide +kernel
theorem pair_25_25_19 : atPair 25 25 19 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_19_0
  · exact chunk_25_25_19_1
  · exact chunk_25_25_19_2
  · exact chunk_25_25_19_3
private theorem chunk_25_25_20_0 :
    atPairChunk 25 25 20 0 test = true := by decide +kernel
private theorem chunk_25_25_20_1 :
    atPairChunk 25 25 20 1 test = true := by decide +kernel
private theorem chunk_25_25_20_2 :
    atPairChunk 25 25 20 2 test = true := by decide +kernel
private theorem chunk_25_25_20_3 :
    atPairChunk 25 25 20 3 test = true := by decide +kernel
theorem pair_25_25_20 : atPair 25 25 20 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_20_0
  · exact chunk_25_25_20_1
  · exact chunk_25_25_20_2
  · exact chunk_25_25_20_3
private theorem chunk_25_25_21_0 :
    atPairChunk 25 25 21 0 test = true := by decide +kernel
private theorem chunk_25_25_21_1 :
    atPairChunk 25 25 21 1 test = true := by decide +kernel
private theorem chunk_25_25_21_2 :
    atPairChunk 25 25 21 2 test = true := by decide +kernel
private theorem chunk_25_25_21_3 :
    atPairChunk 25 25 21 3 test = true := by decide +kernel
theorem pair_25_25_21 : atPair 25 25 21 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_21_0
  · exact chunk_25_25_21_1
  · exact chunk_25_25_21_2
  · exact chunk_25_25_21_3
private theorem chunk_25_25_22_0 :
    atPairChunk 25 25 22 0 test = true := by decide +kernel
private theorem chunk_25_25_22_1 :
    atPairChunk 25 25 22 1 test = true := by decide +kernel
private theorem chunk_25_25_22_2 :
    atPairChunk 25 25 22 2 test = true := by decide +kernel
private theorem chunk_25_25_22_3 :
    atPairChunk 25 25 22 3 test = true := by decide +kernel
theorem pair_25_25_22 : atPair 25 25 22 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_22_0
  · exact chunk_25_25_22_1
  · exact chunk_25_25_22_2
  · exact chunk_25_25_22_3
private theorem chunk_25_25_23_0 :
    atPairChunk 25 25 23 0 test = true := by decide +kernel
private theorem chunk_25_25_23_1 :
    atPairChunk 25 25 23 1 test = true := by decide +kernel
private theorem chunk_25_25_23_2 :
    atPairChunk 25 25 23 2 test = true := by decide +kernel
private theorem chunk_25_25_23_3 :
    atPairChunk 25 25 23 3 test = true := by decide +kernel
theorem pair_25_25_23 : atPair 25 25 23 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_23_0
  · exact chunk_25_25_23_1
  · exact chunk_25_25_23_2
  · exact chunk_25_25_23_3
private theorem chunk_25_25_24_0 :
    atPairChunk 25 25 24 0 test = true := by decide +kernel
private theorem chunk_25_25_24_1 :
    atPairChunk 25 25 24 1 test = true := by decide +kernel
private theorem chunk_25_25_24_2 :
    atPairChunk 25 25 24 2 test = true := by decide +kernel
private theorem chunk_25_25_24_3 :
    atPairChunk 25 25 24 3 test = true := by decide +kernel
theorem pair_25_25_24 : atPair 25 25 24 test = true := by
  apply atPair_of_chunks (by decide)
  intro block hb
  interval_cases block
  · exact chunk_25_25_24_0
  · exact chunk_25_25_24_1
  · exact chunk_25_25_24_2
  · exact chunk_25_25_24_3
end D4Bound.CensusArithmetic
