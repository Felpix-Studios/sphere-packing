import D4Bound.V7CyclicNativeF000
import D4Bound.V7CyclicNativeF001
import D4Bound.V7CyclicNativeF002
import D4Bound.V7CyclicNativeF003
import D4Bound.V7CyclicNativeF004
import D4Bound.V7CyclicNativeF005
import D4Bound.V7CyclicNativeF006
import D4Bound.V7CyclicNativeF011
import D4Bound.V7CyclicNativeF012
import D4Bound.V7CyclicNativeF013
import D4Bound.V7CyclicNativeF014
import D4Bound.V7CyclicNativeF015
import D4Bound.V7CyclicNativeF016
import D4Bound.V7CyclicNativeF022
import D4Bound.V7CyclicNativeF023
import D4Bound.V7CyclicNativeF024
import D4Bound.V7CyclicNativeF025
import D4Bound.V7CyclicNativeF026
import D4Bound.V7CyclicNativeF033
import D4Bound.V7CyclicNativeF034
import D4Bound.V7CyclicNativeF035
import D4Bound.V7CyclicNativeF036
import D4Bound.V7CyclicNativeF044
import D4Bound.V7CyclicNativeF045
import D4Bound.V7CyclicNativeF046
import D4Bound.V7CyclicNativeF055
import D4Bound.V7CyclicNativeF056
import D4Bound.V7CyclicNativeF066
import D4Bound.V7CyclicNativeF111
import D4Bound.V7CyclicNativeF112
import D4Bound.V7CyclicNativeF113
import D4Bound.V7CyclicNativeF114
import D4Bound.V7CyclicNativeF115
import D4Bound.V7CyclicNativeF116
import D4Bound.V7CyclicNativeF122
import D4Bound.V7CyclicNativeF123
import D4Bound.V7CyclicNativeF124
import D4Bound.V7CyclicNativeF125
import D4Bound.V7CyclicNativeF126
import D4Bound.V7CyclicNativeF133
import D4Bound.V7CyclicNativeF134
import D4Bound.V7CyclicNativeF135
import D4Bound.V7CyclicNativeF136
import D4Bound.V7CyclicNativeF144
import D4Bound.V7CyclicNativeF145
import D4Bound.V7CyclicNativeF146
import D4Bound.V7CyclicNativeF155
import D4Bound.V7CyclicNativeF156
import D4Bound.V7CyclicNativeF166
import D4Bound.V7CyclicNativeF222
import D4Bound.V7CyclicNativeF223
import D4Bound.V7CyclicNativeF224
import D4Bound.V7CyclicNativeF225
import D4Bound.V7CyclicNativeF226
import D4Bound.V7CyclicNativeF233
import D4Bound.V7CyclicNativeF234
import D4Bound.V7CyclicNativeF235
import D4Bound.V7CyclicNativeF236
import D4Bound.V7CyclicNativeF244
import D4Bound.V7CyclicNativeF245
import D4Bound.V7CyclicNativeF246
import D4Bound.V7CyclicNativeF255
import D4Bound.V7CyclicNativeF256
import D4Bound.V7CyclicNativeF266
import D4Bound.V7CyclicNativeF333
import D4Bound.V7CyclicNativeF334
import D4Bound.V7CyclicNativeF335
import D4Bound.V7CyclicNativeF336
import D4Bound.V7CyclicNativeF344
import D4Bound.V7CyclicNativeF345
import D4Bound.V7CyclicNativeF346
import D4Bound.V7CyclicNativeF355
import D4Bound.V7CyclicNativeF356
import D4Bound.V7CyclicNativeF366
import D4Bound.V7CyclicNativeF444
import D4Bound.V7CyclicNativeF445
import D4Bound.V7CyclicNativeF446
import D4Bound.V7CyclicNativeF455
import D4Bound.V7CyclicNativeF456
import D4Bound.V7CyclicNativeF466
import D4Bound.V7CyclicNativeF555
import D4Bound.V7CyclicNativeF556
import D4Bound.V7CyclicNativeF566
import D4Bound.V7CyclicNativeF666

/-! `CyclicSign V7.kernel` from the 84 full native checks and the exterior cases. -/
namespace D4Bound.V7
open CyclicNative

/-- The unit of each case module: `caseUnitG` except the per-case overrides. -/
def unitFinal : ℕ → ℕ → ℕ → ℚ
  | 0, 5, 6 => 1/2^0
  | 3, 4, 6 => 1/2^10
  | 3, 5, 6 => 1/2^0
  | 4, 4, 6 => 1/2^10
  | 4, 5, 5 => 1/2^4
  | 4, 5, 6 => 1/2^0
  | 4, 6, 6 => 2^4
  | 5, 5, 5 => 2^6
  | 5, 5, 6 => 1/2^0
  | 5, 6, 6 => 2^14
  | 6, 6, 6 => 2^18
  | p, q, k => caseUnitG p q k

theorem native_full_checks : ∀ p ∈ fullCases,
    fullCheckG capUse (unitFinal p.1 p.2.1 p.2.2) caseFuel p.1 p.2.1 p.2.2 = true := by
  have h000 : fullCheckG capUse (unitFinal 0 0 0) caseFuel 0 0 0 = true :=
    fullCheck000
  have h001 : fullCheckG capUse (unitFinal 0 0 1) caseFuel 0 0 1 = true :=
    fullCheck001
  have h002 : fullCheckG capUse (unitFinal 0 0 2) caseFuel 0 0 2 = true :=
    fullCheck002
  have h003 : fullCheckG capUse (unitFinal 0 0 3) caseFuel 0 0 3 = true :=
    fullCheck003
  have h004 : fullCheckG capUse (unitFinal 0 0 4) caseFuel 0 0 4 = true :=
    fullCheck004
  have h005 : fullCheckG capUse (unitFinal 0 0 5) caseFuel 0 0 5 = true :=
    fullCheck005
  have h006 : fullCheckG capUse (unitFinal 0 0 6) caseFuel 0 0 6 = true :=
    fullCheck006
  have h011 : fullCheckG capUse (unitFinal 0 1 1) caseFuel 0 1 1 = true :=
    fullCheck011
  have h012 : fullCheckG capUse (unitFinal 0 1 2) caseFuel 0 1 2 = true :=
    fullCheck012
  have h013 : fullCheckG capUse (unitFinal 0 1 3) caseFuel 0 1 3 = true :=
    fullCheck013
  have h014 : fullCheckG capUse (unitFinal 0 1 4) caseFuel 0 1 4 = true :=
    fullCheck014
  have h015 : fullCheckG capUse (unitFinal 0 1 5) caseFuel 0 1 5 = true :=
    fullCheck015
  have h016 : fullCheckG capUse (unitFinal 0 1 6) caseFuel 0 1 6 = true :=
    fullCheck016
  have h022 : fullCheckG capUse (unitFinal 0 2 2) caseFuel 0 2 2 = true :=
    fullCheck022
  have h023 : fullCheckG capUse (unitFinal 0 2 3) caseFuel 0 2 3 = true :=
    fullCheck023
  have h024 : fullCheckG capUse (unitFinal 0 2 4) caseFuel 0 2 4 = true :=
    fullCheck024
  have h025 : fullCheckG capUse (unitFinal 0 2 5) caseFuel 0 2 5 = true :=
    fullCheck025
  have h026 : fullCheckG capUse (unitFinal 0 2 6) caseFuel 0 2 6 = true :=
    fullCheck026
  have h033 : fullCheckG capUse (unitFinal 0 3 3) caseFuel 0 3 3 = true :=
    fullCheck033
  have h034 : fullCheckG capUse (unitFinal 0 3 4) caseFuel 0 3 4 = true :=
    fullCheck034
  have h035 : fullCheckG capUse (unitFinal 0 3 5) caseFuel 0 3 5 = true :=
    fullCheck035
  have h036 : fullCheckG capUse (unitFinal 0 3 6) caseFuel 0 3 6 = true :=
    fullCheck036
  have h044 : fullCheckG capUse (unitFinal 0 4 4) caseFuel 0 4 4 = true :=
    fullCheck044
  have h045 : fullCheckG capUse (unitFinal 0 4 5) caseFuel 0 4 5 = true :=
    fullCheck045
  have h046 : fullCheckG capUse (unitFinal 0 4 6) caseFuel 0 4 6 = true :=
    fullCheck046
  have h055 : fullCheckG capUse (unitFinal 0 5 5) caseFuel 0 5 5 = true :=
    fullCheck055
  have h056 : fullCheckG capUse (unitFinal 0 5 6) caseFuel 0 5 6 = true :=
    fullCheck056
  have h066 : fullCheckG capUse (unitFinal 0 6 6) caseFuel 0 6 6 = true :=
    fullCheck066
  have h111 : fullCheckG capUse (unitFinal 1 1 1) caseFuel 1 1 1 = true :=
    fullCheck111
  have h112 : fullCheckG capUse (unitFinal 1 1 2) caseFuel 1 1 2 = true :=
    fullCheck112
  have h113 : fullCheckG capUse (unitFinal 1 1 3) caseFuel 1 1 3 = true :=
    fullCheck113
  have h114 : fullCheckG capUse (unitFinal 1 1 4) caseFuel 1 1 4 = true :=
    fullCheck114
  have h115 : fullCheckG capUse (unitFinal 1 1 5) caseFuel 1 1 5 = true :=
    fullCheck115
  have h116 : fullCheckG capUse (unitFinal 1 1 6) caseFuel 1 1 6 = true :=
    fullCheck116
  have h122 : fullCheckG capUse (unitFinal 1 2 2) caseFuel 1 2 2 = true :=
    fullCheck122
  have h123 : fullCheckG capUse (unitFinal 1 2 3) caseFuel 1 2 3 = true :=
    fullCheck123
  have h124 : fullCheckG capUse (unitFinal 1 2 4) caseFuel 1 2 4 = true :=
    fullCheck124
  have h125 : fullCheckG capUse (unitFinal 1 2 5) caseFuel 1 2 5 = true :=
    fullCheck125
  have h126 : fullCheckG capUse (unitFinal 1 2 6) caseFuel 1 2 6 = true :=
    fullCheck126
  have h133 : fullCheckG capUse (unitFinal 1 3 3) caseFuel 1 3 3 = true :=
    fullCheck133
  have h134 : fullCheckG capUse (unitFinal 1 3 4) caseFuel 1 3 4 = true :=
    fullCheck134
  have h135 : fullCheckG capUse (unitFinal 1 3 5) caseFuel 1 3 5 = true :=
    fullCheck135
  have h136 : fullCheckG capUse (unitFinal 1 3 6) caseFuel 1 3 6 = true :=
    fullCheck136
  have h144 : fullCheckG capUse (unitFinal 1 4 4) caseFuel 1 4 4 = true :=
    fullCheck144
  have h145 : fullCheckG capUse (unitFinal 1 4 5) caseFuel 1 4 5 = true :=
    fullCheck145
  have h146 : fullCheckG capUse (unitFinal 1 4 6) caseFuel 1 4 6 = true :=
    fullCheck146
  have h155 : fullCheckG capUse (unitFinal 1 5 5) caseFuel 1 5 5 = true :=
    fullCheck155
  have h156 : fullCheckG capUse (unitFinal 1 5 6) caseFuel 1 5 6 = true :=
    fullCheck156
  have h166 : fullCheckG capUse (unitFinal 1 6 6) caseFuel 1 6 6 = true :=
    fullCheck166
  have h222 : fullCheckG capUse (unitFinal 2 2 2) caseFuel 2 2 2 = true :=
    fullCheck222
  have h223 : fullCheckG capUse (unitFinal 2 2 3) caseFuel 2 2 3 = true :=
    fullCheck223
  have h224 : fullCheckG capUse (unitFinal 2 2 4) caseFuel 2 2 4 = true :=
    fullCheck224
  have h225 : fullCheckG capUse (unitFinal 2 2 5) caseFuel 2 2 5 = true :=
    fullCheck225
  have h226 : fullCheckG capUse (unitFinal 2 2 6) caseFuel 2 2 6 = true :=
    fullCheck226
  have h233 : fullCheckG capUse (unitFinal 2 3 3) caseFuel 2 3 3 = true :=
    fullCheck233
  have h234 : fullCheckG capUse (unitFinal 2 3 4) caseFuel 2 3 4 = true :=
    fullCheck234
  have h235 : fullCheckG capUse (unitFinal 2 3 5) caseFuel 2 3 5 = true :=
    fullCheck235
  have h236 : fullCheckG capUse (unitFinal 2 3 6) caseFuel 2 3 6 = true :=
    fullCheck236
  have h244 : fullCheckG capUse (unitFinal 2 4 4) caseFuel 2 4 4 = true :=
    fullCheck244
  have h245 : fullCheckG capUse (unitFinal 2 4 5) caseFuel 2 4 5 = true :=
    fullCheck245
  have h246 : fullCheckG capUse (unitFinal 2 4 6) caseFuel 2 4 6 = true :=
    fullCheck246
  have h255 : fullCheckG capUse (unitFinal 2 5 5) caseFuel 2 5 5 = true :=
    fullCheck255
  have h256 : fullCheckG capUse (unitFinal 2 5 6) caseFuel 2 5 6 = true :=
    fullCheck256
  have h266 : fullCheckG capUse (unitFinal 2 6 6) caseFuel 2 6 6 = true :=
    fullCheck266
  have h333 : fullCheckG capUse (unitFinal 3 3 3) caseFuel 3 3 3 = true :=
    fullCheck333
  have h334 : fullCheckG capUse (unitFinal 3 3 4) caseFuel 3 3 4 = true :=
    fullCheck334
  have h335 : fullCheckG capUse (unitFinal 3 3 5) caseFuel 3 3 5 = true :=
    fullCheck335
  have h336 : fullCheckG capUse (unitFinal 3 3 6) caseFuel 3 3 6 = true :=
    fullCheck336
  have h344 : fullCheckG capUse (unitFinal 3 4 4) caseFuel 3 4 4 = true :=
    fullCheck344
  have h345 : fullCheckG capUse (unitFinal 3 4 5) caseFuel 3 4 5 = true :=
    fullCheck345
  have h346 : fullCheckG capUse (unitFinal 3 4 6) caseFuel 3 4 6 = true :=
    fullCheck346
  have h355 : fullCheckG capUse (unitFinal 3 5 5) caseFuel 3 5 5 = true :=
    fullCheck355
  have h356 : fullCheckG capUse (unitFinal 3 5 6) caseFuel 3 5 6 = true :=
    fullCheck356
  have h366 : fullCheckG capUse (unitFinal 3 6 6) caseFuel 3 6 6 = true :=
    fullCheck366
  have h444 : fullCheckG capUse (unitFinal 4 4 4) caseFuel 4 4 4 = true :=
    fullCheck444
  have h445 : fullCheckG capUse (unitFinal 4 4 5) caseFuel 4 4 5 = true :=
    fullCheck445
  have h446 : fullCheckG capUse (unitFinal 4 4 6) caseFuel 4 4 6 = true :=
    fullCheck446
  have h455 : fullCheckG capUse (unitFinal 4 5 5) caseFuel 4 5 5 = true :=
    fullCheck455
  have h456 : fullCheckG capUse (unitFinal 4 5 6) caseFuel 4 5 6 = true :=
    fullCheck456
  have h466 : fullCheckG capUse (unitFinal 4 6 6) caseFuel 4 6 6 = true :=
    fullCheck466
  have h555 : fullCheckG capUse (unitFinal 5 5 5) caseFuel 5 5 5 = true :=
    fullCheck555
  have h556 : fullCheckG capUse (unitFinal 5 5 6) caseFuel 5 5 6 = true :=
    fullCheck556
  have h566 : fullCheckG capUse (unitFinal 5 6 6) caseFuel 5 6 6 = true :=
    fullCheck566
  have h666 : fullCheckG capUse (unitFinal 6 6 6) caseFuel 6 6 6 = true :=
    fullCheck666
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ hp
  simp only [fullCases, Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk] at hp
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | assumption

/-- The cyclic sign of the concrete V7 kernel, given the 28 exterior cases. -/
theorem v7_cyclic_sign_of_outside (outside : ∀ p ∈ outsideCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.val s →
      r ≤ s → 7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) : CyclicSign kernel := by
  apply cyclicSign_of_112_cases _ outside
  intro p hp r s d hr hs hd _ _
  exact full_case_of_G p.1 p.2.1 p.2.2 p.1.isLt p.2.1.isLt p.2.2.isLt capUse _ caseFuel
    (native_full_checks p hp) hr hs hd

end D4Bound.V7

#print axioms D4Bound.V7.v7_cyclic_sign_of_outside
