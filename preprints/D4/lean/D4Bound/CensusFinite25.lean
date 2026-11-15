import D4Bound.CensusFinite25Part0
import D4Bound.CensusFinite25Part1
import D4Bound.CensusFinite25Part2
import D4Bound.CensusFinite25Part3
import Mathlib.Tactic.IntervalCases
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.CensusArithmetic
theorem census_N25 : allAt 25 test = true := by
  apply allAt_of_pairs
  intro n3 h3 n2 h2
  change n3 ≤ 25 at h3
  interval_cases n3
  · change n2 ≤ 0 at h2
    interval_cases n2
    · exact pair_25_0_0
  · change n2 ≤ 1 at h2
    interval_cases n2
    · exact pair_25_1_0
    · exact pair_25_1_1
  · change n2 ≤ 2 at h2
    interval_cases n2
    · exact pair_25_2_0
    · exact pair_25_2_1
    · exact pair_25_2_2
  · change n2 ≤ 3 at h2
    interval_cases n2
    · exact pair_25_3_0
    · exact pair_25_3_1
    · exact pair_25_3_2
    · exact pair_25_3_3
  · change n2 ≤ 4 at h2
    interval_cases n2
    · exact pair_25_4_0
    · exact pair_25_4_1
    · exact pair_25_4_2
    · exact pair_25_4_3
    · exact pair_25_4_4
  · change n2 ≤ 5 at h2
    interval_cases n2
    · exact pair_25_5_0
    · exact pair_25_5_1
    · exact pair_25_5_2
    · exact pair_25_5_3
    · exact pair_25_5_4
    · exact pair_25_5_5
  · change n2 ≤ 6 at h2
    interval_cases n2
    · exact pair_25_6_0
    · exact pair_25_6_1
    · exact pair_25_6_2
    · exact pair_25_6_3
    · exact pair_25_6_4
    · exact pair_25_6_5
    · exact pair_25_6_6
  · change n2 ≤ 7 at h2
    interval_cases n2
    · exact pair_25_7_0
    · exact pair_25_7_1
    · exact pair_25_7_2
    · exact pair_25_7_3
    · exact pair_25_7_4
    · exact pair_25_7_5
    · exact pair_25_7_6
    · exact pair_25_7_7
  · change n2 ≤ 8 at h2
    interval_cases n2
    · exact pair_25_8_0
    · exact pair_25_8_1
    · exact pair_25_8_2
    · exact pair_25_8_3
    · exact pair_25_8_4
    · exact pair_25_8_5
    · exact pair_25_8_6
    · exact pair_25_8_7
    · exact pair_25_8_8
  · change n2 ≤ 9 at h2
    interval_cases n2
    · exact pair_25_9_0
    · exact pair_25_9_1
    · exact pair_25_9_2
    · exact pair_25_9_3
    · exact pair_25_9_4
    · exact pair_25_9_5
    · exact pair_25_9_6
    · exact pair_25_9_7
    · exact pair_25_9_8
    · exact pair_25_9_9
  · change n2 ≤ 10 at h2
    interval_cases n2
    · exact pair_25_10_0
    · exact pair_25_10_1
    · exact pair_25_10_2
    · exact pair_25_10_3
    · exact pair_25_10_4
    · exact pair_25_10_5
    · exact pair_25_10_6
    · exact pair_25_10_7
    · exact pair_25_10_8
    · exact pair_25_10_9
    · exact pair_25_10_10
  · change n2 ≤ 11 at h2
    interval_cases n2
    · exact pair_25_11_0
    · exact pair_25_11_1
    · exact pair_25_11_2
    · exact pair_25_11_3
    · exact pair_25_11_4
    · exact pair_25_11_5
    · exact pair_25_11_6
    · exact pair_25_11_7
    · exact pair_25_11_8
    · exact pair_25_11_9
    · exact pair_25_11_10
    · exact pair_25_11_11
  · change n2 ≤ 12 at h2
    interval_cases n2
    · exact pair_25_12_0
    · exact pair_25_12_1
    · exact pair_25_12_2
    · exact pair_25_12_3
    · exact pair_25_12_4
    · exact pair_25_12_5
    · exact pair_25_12_6
    · exact pair_25_12_7
    · exact pair_25_12_8
    · exact pair_25_12_9
    · exact pair_25_12_10
    · exact pair_25_12_11
    · exact pair_25_12_12
  · change n2 ≤ 13 at h2
    interval_cases n2
    · exact pair_25_13_0
    · exact pair_25_13_1
    · exact pair_25_13_2
    · exact pair_25_13_3
    · exact pair_25_13_4
    · exact pair_25_13_5
    · exact pair_25_13_6
    · exact pair_25_13_7
    · exact pair_25_13_8
    · exact pair_25_13_9
    · exact pair_25_13_10
    · exact pair_25_13_11
    · exact pair_25_13_12
    · exact pair_25_13_13
  · change n2 ≤ 14 at h2
    interval_cases n2
    · exact pair_25_14_0
    · exact pair_25_14_1
    · exact pair_25_14_2
    · exact pair_25_14_3
    · exact pair_25_14_4
    · exact pair_25_14_5
    · exact pair_25_14_6
    · exact pair_25_14_7
    · exact pair_25_14_8
    · exact pair_25_14_9
    · exact pair_25_14_10
    · exact pair_25_14_11
    · exact pair_25_14_12
    · exact pair_25_14_13
    · exact pair_25_14_14
  · change n2 ≤ 15 at h2
    interval_cases n2
    · exact pair_25_15_0
    · exact pair_25_15_1
    · exact pair_25_15_2
    · exact pair_25_15_3
    · exact pair_25_15_4
    · exact pair_25_15_5
    · exact pair_25_15_6
    · exact pair_25_15_7
    · exact pair_25_15_8
    · exact pair_25_15_9
    · exact pair_25_15_10
    · exact pair_25_15_11
    · exact pair_25_15_12
    · exact pair_25_15_13
    · exact pair_25_15_14
    · exact pair_25_15_15
  · change n2 ≤ 16 at h2
    interval_cases n2
    · exact pair_25_16_0
    · exact pair_25_16_1
    · exact pair_25_16_2
    · exact pair_25_16_3
    · exact pair_25_16_4
    · exact pair_25_16_5
    · exact pair_25_16_6
    · exact pair_25_16_7
    · exact pair_25_16_8
    · exact pair_25_16_9
    · exact pair_25_16_10
    · exact pair_25_16_11
    · exact pair_25_16_12
    · exact pair_25_16_13
    · exact pair_25_16_14
    · exact pair_25_16_15
    · exact pair_25_16_16
  · change n2 ≤ 17 at h2
    interval_cases n2
    · exact pair_25_17_0
    · exact pair_25_17_1
    · exact pair_25_17_2
    · exact pair_25_17_3
    · exact pair_25_17_4
    · exact pair_25_17_5
    · exact pair_25_17_6
    · exact pair_25_17_7
    · exact pair_25_17_8
    · exact pair_25_17_9
    · exact pair_25_17_10
    · exact pair_25_17_11
    · exact pair_25_17_12
    · exact pair_25_17_13
    · exact pair_25_17_14
    · exact pair_25_17_15
    · exact pair_25_17_16
    · exact pair_25_17_17
  · change n2 ≤ 18 at h2
    interval_cases n2
    · exact pair_25_18_0
    · exact pair_25_18_1
    · exact pair_25_18_2
    · exact pair_25_18_3
    · exact pair_25_18_4
    · exact pair_25_18_5
    · exact pair_25_18_6
    · exact pair_25_18_7
    · exact pair_25_18_8
    · exact pair_25_18_9
    · exact pair_25_18_10
    · exact pair_25_18_11
    · exact pair_25_18_12
    · exact pair_25_18_13
    · exact pair_25_18_14
    · exact pair_25_18_15
    · exact pair_25_18_16
    · exact pair_25_18_17
    · exact pair_25_18_18
  · change n2 ≤ 19 at h2
    interval_cases n2
    · exact pair_25_19_0
    · exact pair_25_19_1
    · exact pair_25_19_2
    · exact pair_25_19_3
    · exact pair_25_19_4
    · exact pair_25_19_5
    · exact pair_25_19_6
    · exact pair_25_19_7
    · exact pair_25_19_8
    · exact pair_25_19_9
    · exact pair_25_19_10
    · exact pair_25_19_11
    · exact pair_25_19_12
    · exact pair_25_19_13
    · exact pair_25_19_14
    · exact pair_25_19_15
    · exact pair_25_19_16
    · exact pair_25_19_17
    · exact pair_25_19_18
    · exact pair_25_19_19
  · change n2 ≤ 20 at h2
    interval_cases n2
    · exact pair_25_20_0
    · exact pair_25_20_1
    · exact pair_25_20_2
    · exact pair_25_20_3
    · exact pair_25_20_4
    · exact pair_25_20_5
    · exact pair_25_20_6
    · exact pair_25_20_7
    · exact pair_25_20_8
    · exact pair_25_20_9
    · exact pair_25_20_10
    · exact pair_25_20_11
    · exact pair_25_20_12
    · exact pair_25_20_13
    · exact pair_25_20_14
    · exact pair_25_20_15
    · exact pair_25_20_16
    · exact pair_25_20_17
    · exact pair_25_20_18
    · exact pair_25_20_19
    · exact pair_25_20_20
  · change n2 ≤ 21 at h2
    interval_cases n2
    · exact pair_25_21_0
    · exact pair_25_21_1
    · exact pair_25_21_2
    · exact pair_25_21_3
    · exact pair_25_21_4
    · exact pair_25_21_5
    · exact pair_25_21_6
    · exact pair_25_21_7
    · exact pair_25_21_8
    · exact pair_25_21_9
    · exact pair_25_21_10
    · exact pair_25_21_11
    · exact pair_25_21_12
    · exact pair_25_21_13
    · exact pair_25_21_14
    · exact pair_25_21_15
    · exact pair_25_21_16
    · exact pair_25_21_17
    · exact pair_25_21_18
    · exact pair_25_21_19
    · exact pair_25_21_20
    · exact pair_25_21_21
  · change n2 ≤ 22 at h2
    interval_cases n2
    · exact pair_25_22_0
    · exact pair_25_22_1
    · exact pair_25_22_2
    · exact pair_25_22_3
    · exact pair_25_22_4
    · exact pair_25_22_5
    · exact pair_25_22_6
    · exact pair_25_22_7
    · exact pair_25_22_8
    · exact pair_25_22_9
    · exact pair_25_22_10
    · exact pair_25_22_11
    · exact pair_25_22_12
    · exact pair_25_22_13
    · exact pair_25_22_14
    · exact pair_25_22_15
    · exact pair_25_22_16
    · exact pair_25_22_17
    · exact pair_25_22_18
    · exact pair_25_22_19
    · exact pair_25_22_20
    · exact pair_25_22_21
    · exact pair_25_22_22
  · change n2 ≤ 23 at h2
    interval_cases n2
    · exact pair_25_23_0
    · exact pair_25_23_1
    · exact pair_25_23_2
    · exact pair_25_23_3
    · exact pair_25_23_4
    · exact pair_25_23_5
    · exact pair_25_23_6
    · exact pair_25_23_7
    · exact pair_25_23_8
    · exact pair_25_23_9
    · exact pair_25_23_10
    · exact pair_25_23_11
    · exact pair_25_23_12
    · exact pair_25_23_13
    · exact pair_25_23_14
    · exact pair_25_23_15
    · exact pair_25_23_16
    · exact pair_25_23_17
    · exact pair_25_23_18
    · exact pair_25_23_19
    · exact pair_25_23_20
    · exact pair_25_23_21
    · exact pair_25_23_22
    · exact pair_25_23_23
  · change n2 ≤ 24 at h2
    interval_cases n2
    · exact pair_25_24_0
    · exact pair_25_24_1
    · exact pair_25_24_2
    · exact pair_25_24_3
    · exact pair_25_24_4
    · exact pair_25_24_5
    · exact pair_25_24_6
    · exact pair_25_24_7
    · exact pair_25_24_8
    · exact pair_25_24_9
    · exact pair_25_24_10
    · exact pair_25_24_11
    · exact pair_25_24_12
    · exact pair_25_24_13
    · exact pair_25_24_14
    · exact pair_25_24_15
    · exact pair_25_24_16
    · exact pair_25_24_17
    · exact pair_25_24_18
    · exact pair_25_24_19
    · exact pair_25_24_20
    · exact pair_25_24_21
    · exact pair_25_24_22
    · exact pair_25_24_23
    · exact pair_25_24_24
  · change n2 ≤ 24 at h2
    interval_cases n2
    · exact pair_25_25_0
    · exact pair_25_25_1
    · exact pair_25_25_2
    · exact pair_25_25_3
    · exact pair_25_25_4
    · exact pair_25_25_5
    · exact pair_25_25_6
    · exact pair_25_25_7
    · exact pair_25_25_8
    · exact pair_25_25_9
    · exact pair_25_25_10
    · exact pair_25_25_11
    · exact pair_25_25_12
    · exact pair_25_25_13
    · exact pair_25_25_14
    · exact pair_25_25_15
    · exact pair_25_25_16
    · exact pair_25_25_17
    · exact pair_25_25_18
    · exact pair_25_25_19
    · exact pair_25_25_20
    · exact pair_25_25_21
    · exact pair_25_25_22
    · exact pair_25_25_23
    · exact pair_25_25_24
end D4Bound.CensusArithmetic
