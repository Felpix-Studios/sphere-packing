import D4Bound.CensusFinite22Part0
import D4Bound.CensusFinite22Part1
import D4Bound.CensusFinite22Part2
import Mathlib.Tactic.IntervalCases
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.CensusArithmetic
theorem census_N22 : allAt 22 test = true := by
  apply allAt_of_pairs
  intro n3 h3 n2 h2
  change n3 ≤ 22 at h3
  interval_cases n3
  · change n2 ≤ 0 at h2
    interval_cases n2
    · exact pair_22_0_0
  · change n2 ≤ 1 at h2
    interval_cases n2
    · exact pair_22_1_0
    · exact pair_22_1_1
  · change n2 ≤ 2 at h2
    interval_cases n2
    · exact pair_22_2_0
    · exact pair_22_2_1
    · exact pair_22_2_2
  · change n2 ≤ 3 at h2
    interval_cases n2
    · exact pair_22_3_0
    · exact pair_22_3_1
    · exact pair_22_3_2
    · exact pair_22_3_3
  · change n2 ≤ 4 at h2
    interval_cases n2
    · exact pair_22_4_0
    · exact pair_22_4_1
    · exact pair_22_4_2
    · exact pair_22_4_3
    · exact pair_22_4_4
  · change n2 ≤ 5 at h2
    interval_cases n2
    · exact pair_22_5_0
    · exact pair_22_5_1
    · exact pair_22_5_2
    · exact pair_22_5_3
    · exact pair_22_5_4
    · exact pair_22_5_5
  · change n2 ≤ 6 at h2
    interval_cases n2
    · exact pair_22_6_0
    · exact pair_22_6_1
    · exact pair_22_6_2
    · exact pair_22_6_3
    · exact pair_22_6_4
    · exact pair_22_6_5
    · exact pair_22_6_6
  · change n2 ≤ 7 at h2
    interval_cases n2
    · exact pair_22_7_0
    · exact pair_22_7_1
    · exact pair_22_7_2
    · exact pair_22_7_3
    · exact pair_22_7_4
    · exact pair_22_7_5
    · exact pair_22_7_6
    · exact pair_22_7_7
  · change n2 ≤ 8 at h2
    interval_cases n2
    · exact pair_22_8_0
    · exact pair_22_8_1
    · exact pair_22_8_2
    · exact pair_22_8_3
    · exact pair_22_8_4
    · exact pair_22_8_5
    · exact pair_22_8_6
    · exact pair_22_8_7
    · exact pair_22_8_8
  · change n2 ≤ 9 at h2
    interval_cases n2
    · exact pair_22_9_0
    · exact pair_22_9_1
    · exact pair_22_9_2
    · exact pair_22_9_3
    · exact pair_22_9_4
    · exact pair_22_9_5
    · exact pair_22_9_6
    · exact pair_22_9_7
    · exact pair_22_9_8
    · exact pair_22_9_9
  · change n2 ≤ 10 at h2
    interval_cases n2
    · exact pair_22_10_0
    · exact pair_22_10_1
    · exact pair_22_10_2
    · exact pair_22_10_3
    · exact pair_22_10_4
    · exact pair_22_10_5
    · exact pair_22_10_6
    · exact pair_22_10_7
    · exact pair_22_10_8
    · exact pair_22_10_9
    · exact pair_22_10_10
  · change n2 ≤ 11 at h2
    interval_cases n2
    · exact pair_22_11_0
    · exact pair_22_11_1
    · exact pair_22_11_2
    · exact pair_22_11_3
    · exact pair_22_11_4
    · exact pair_22_11_5
    · exact pair_22_11_6
    · exact pair_22_11_7
    · exact pair_22_11_8
    · exact pair_22_11_9
    · exact pair_22_11_10
    · exact pair_22_11_11
  · change n2 ≤ 12 at h2
    interval_cases n2
    · exact pair_22_12_0
    · exact pair_22_12_1
    · exact pair_22_12_2
    · exact pair_22_12_3
    · exact pair_22_12_4
    · exact pair_22_12_5
    · exact pair_22_12_6
    · exact pair_22_12_7
    · exact pair_22_12_8
    · exact pair_22_12_9
    · exact pair_22_12_10
    · exact pair_22_12_11
    · exact pair_22_12_12
  · change n2 ≤ 13 at h2
    interval_cases n2
    · exact pair_22_13_0
    · exact pair_22_13_1
    · exact pair_22_13_2
    · exact pair_22_13_3
    · exact pair_22_13_4
    · exact pair_22_13_5
    · exact pair_22_13_6
    · exact pair_22_13_7
    · exact pair_22_13_8
    · exact pair_22_13_9
    · exact pair_22_13_10
    · exact pair_22_13_11
    · exact pair_22_13_12
    · exact pair_22_13_13
  · change n2 ≤ 14 at h2
    interval_cases n2
    · exact pair_22_14_0
    · exact pair_22_14_1
    · exact pair_22_14_2
    · exact pair_22_14_3
    · exact pair_22_14_4
    · exact pair_22_14_5
    · exact pair_22_14_6
    · exact pair_22_14_7
    · exact pair_22_14_8
    · exact pair_22_14_9
    · exact pair_22_14_10
    · exact pair_22_14_11
    · exact pair_22_14_12
    · exact pair_22_14_13
    · exact pair_22_14_14
  · change n2 ≤ 15 at h2
    interval_cases n2
    · exact pair_22_15_0
    · exact pair_22_15_1
    · exact pair_22_15_2
    · exact pair_22_15_3
    · exact pair_22_15_4
    · exact pair_22_15_5
    · exact pair_22_15_6
    · exact pair_22_15_7
    · exact pair_22_15_8
    · exact pair_22_15_9
    · exact pair_22_15_10
    · exact pair_22_15_11
    · exact pair_22_15_12
    · exact pair_22_15_13
    · exact pair_22_15_14
    · exact pair_22_15_15
  · change n2 ≤ 16 at h2
    interval_cases n2
    · exact pair_22_16_0
    · exact pair_22_16_1
    · exact pair_22_16_2
    · exact pair_22_16_3
    · exact pair_22_16_4
    · exact pair_22_16_5
    · exact pair_22_16_6
    · exact pair_22_16_7
    · exact pair_22_16_8
    · exact pair_22_16_9
    · exact pair_22_16_10
    · exact pair_22_16_11
    · exact pair_22_16_12
    · exact pair_22_16_13
    · exact pair_22_16_14
    · exact pair_22_16_15
    · exact pair_22_16_16
  · change n2 ≤ 17 at h2
    interval_cases n2
    · exact pair_22_17_0
    · exact pair_22_17_1
    · exact pair_22_17_2
    · exact pair_22_17_3
    · exact pair_22_17_4
    · exact pair_22_17_5
    · exact pair_22_17_6
    · exact pair_22_17_7
    · exact pair_22_17_8
    · exact pair_22_17_9
    · exact pair_22_17_10
    · exact pair_22_17_11
    · exact pair_22_17_12
    · exact pair_22_17_13
    · exact pair_22_17_14
    · exact pair_22_17_15
    · exact pair_22_17_16
    · exact pair_22_17_17
  · change n2 ≤ 18 at h2
    interval_cases n2
    · exact pair_22_18_0
    · exact pair_22_18_1
    · exact pair_22_18_2
    · exact pair_22_18_3
    · exact pair_22_18_4
    · exact pair_22_18_5
    · exact pair_22_18_6
    · exact pair_22_18_7
    · exact pair_22_18_8
    · exact pair_22_18_9
    · exact pair_22_18_10
    · exact pair_22_18_11
    · exact pair_22_18_12
    · exact pair_22_18_13
    · exact pair_22_18_14
    · exact pair_22_18_15
    · exact pair_22_18_16
    · exact pair_22_18_17
    · exact pair_22_18_18
  · change n2 ≤ 19 at h2
    interval_cases n2
    · exact pair_22_19_0
    · exact pair_22_19_1
    · exact pair_22_19_2
    · exact pair_22_19_3
    · exact pair_22_19_4
    · exact pair_22_19_5
    · exact pair_22_19_6
    · exact pair_22_19_7
    · exact pair_22_19_8
    · exact pair_22_19_9
    · exact pair_22_19_10
    · exact pair_22_19_11
    · exact pair_22_19_12
    · exact pair_22_19_13
    · exact pair_22_19_14
    · exact pair_22_19_15
    · exact pair_22_19_16
    · exact pair_22_19_17
    · exact pair_22_19_18
    · exact pair_22_19_19
  · change n2 ≤ 20 at h2
    interval_cases n2
    · exact pair_22_20_0
    · exact pair_22_20_1
    · exact pair_22_20_2
    · exact pair_22_20_3
    · exact pair_22_20_4
    · exact pair_22_20_5
    · exact pair_22_20_6
    · exact pair_22_20_7
    · exact pair_22_20_8
    · exact pair_22_20_9
    · exact pair_22_20_10
    · exact pair_22_20_11
    · exact pair_22_20_12
    · exact pair_22_20_13
    · exact pair_22_20_14
    · exact pair_22_20_15
    · exact pair_22_20_16
    · exact pair_22_20_17
    · exact pair_22_20_18
    · exact pair_22_20_19
    · exact pair_22_20_20
  · change n2 ≤ 21 at h2
    interval_cases n2
    · exact pair_22_21_0
    · exact pair_22_21_1
    · exact pair_22_21_2
    · exact pair_22_21_3
    · exact pair_22_21_4
    · exact pair_22_21_5
    · exact pair_22_21_6
    · exact pair_22_21_7
    · exact pair_22_21_8
    · exact pair_22_21_9
    · exact pair_22_21_10
    · exact pair_22_21_11
    · exact pair_22_21_12
    · exact pair_22_21_13
    · exact pair_22_21_14
    · exact pair_22_21_15
    · exact pair_22_21_16
    · exact pair_22_21_17
    · exact pair_22_21_18
    · exact pair_22_21_19
    · exact pair_22_21_20
    · exact pair_22_21_21
  · change n2 ≤ 22 at h2
    interval_cases n2
    · exact pair_22_22_0
    · exact pair_22_22_1
    · exact pair_22_22_2
    · exact pair_22_22_3
    · exact pair_22_22_4
    · exact pair_22_22_5
    · exact pair_22_22_6
    · exact pair_22_22_7
    · exact pair_22_22_8
    · exact pair_22_22_9
    · exact pair_22_22_10
    · exact pair_22_22_11
    · exact pair_22_22_12
    · exact pair_22_22_13
    · exact pair_22_22_14
    · exact pair_22_22_15
    · exact pair_22_22_16
    · exact pair_22_22_17
    · exact pair_22_22_18
    · exact pair_22_22_19
    · exact pair_22_22_20
    · exact pair_22_22_21
    · exact pair_22_22_22
end D4Bound.CensusArithmetic
