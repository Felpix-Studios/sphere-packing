import D4Bound.AnnularCert

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

open Finset

namespace D4Bound.ModerateGraphCertificate

noncomputable section

open AnnularCertificate

def coefficients : Fin 16 → ℝ := ![(435943391981/400000000000), (118597037099/120000000000), (4896096758941/4000000000000), (356409633577/250000000000), (5913407203459/6000000000000), (1489385735239/1750000000000), (4665259054323/8000000000000), (178203421627/900000000000), (16516182971/200000000000), (0/1), (0/1), (0/1), (1338876016223/14000000000000), (1016195222447/15000000000000), (700900327883/16000000000000), (1081981466309/17000000000000)]

def rest (t : ℝ) : ℝ := ∑ i : Fin 16, coefficients i * (Polynomial.Chebyshev.U ℝ ((i.val+1 : ℕ) : ℤ)).eval t

theorem rest_energy : SphereEnergyNonneg rest := by
  apply sphereEnergy_sum
  intro i _
  fin_cases i <;> norm_num [coefficients]

theorem diagonal : (109916026941/500000000000) + rest 1 = (40670769968163/1000000000000) := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, Polynomial.Chebyshev.U_eval_one]

def wholeNumerators : List ℤ := [407237834404951550945805534975, 39288264673255583246673515187840, -4473838873190659560773515891287552, 144815004472451965875426729481003008, -2263334709882341785362321723063533568, 21001108662585846235647930893221232640, -127786465107748259431575501354030858240, 539335618989379349063084669942322167808, -1633242645217865395217931137518216937472, 3618778984417254886544677703259669921792, -5917620480660765326399498752374456975360, 7131466621348977819119694993216346521600, -6253542204034445002953148813244268281856, 3879359810460611983459539872150930325504, -1613015008430571355990964336358970097664, 403168850005167667630170950530121072640, -45781236583790613771455759495137853440]

def wholeDenominator : ℤ := 1102547012366845395000000000000

def wholeLeaves : List (ℕ × ℕ × ℕ) := [(0, 7, 1), (1, 7, 1), (2, 7, 1), (3, 7, 1), (8, 8, 1), (18, 9, 1), (38, 10, 1), (78, 11, 1), (158, 12, 1), (159, 12, 1), (320, 13, 1), (321, 13, 1), (322, 13, 1), (323, 13, 1), (81, 11, 1), (41, 10, 1), (21, 9, 1), (11, 8, 1), (3, 6, 1), (1, 4, 1), (2, 4, 1), (3, 4, 1), (4, 4, 1), (10, 5, 1), (11, 5, 1), (24, 6, 1), (25, 6, 1), (52, 7, 1), (106, 8, 1), (107, 8, 1), (216, 9, 1), (217, 9, 1), (436, 10, 1), (874, 11, 1), (875, 11, 1), (876, 11, 1), (877, 11, 1), (439, 10, 1), (55, 7, 1), (14, 5, 1), (15, 5, 1), (16, 5, 1), (34, 6, 1), (70, 7, 1), (284, 9, 1), (285, 9, 1), (572, 10, 1), (573, 10, 1), (574, 10, 1), (575, 10, 1), (9, 4, 1), (10, 4, 1), (22, 5, 1), (92, 7, 1), (93, 7, 1), (188, 8, 1), (189, 8, 1), (380, 9, 1), (762, 10, 1), (763, 10, 1), (764, 10, 1), (765, 10, 1), (383, 9, 1), (24, 5, 1), (25, 5, 1), (52, 6, 1), (106, 7, 1), (428, 9, 1), (858, 10, 1), (859, 10, 1), (1720, 11, 1), (1721, 11, 1), (861, 10, 1), (431, 9, 1), (27, 5, 1), (14, 4, 1), (30, 5, 1), (62, 6, 1), (126, 7, 1), (254, 8, 1), (255, 8, 1)]

theorem whole_checked : chainOK wholeNumerators 0 0 wholeLeaves 1 0 = true := by decide +kernel

theorem whole_endpoint : 0 < evalZ wholeNumerators 1 := by norm_num [wholeNumerators, evalZ]

theorem whole_identity (u : ℝ) :
    (109916026941/500000000000) + rest ((-1/1)+(16/9)*u) + (0/1) =
      -evalZ wholeNumerators u / wholeDenominator := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, wholeNumerators, wholeDenominator, evalZ]
  <;> ring

theorem whole_sign (t : ℝ) (ht0 : (-1/1) ≤ t) (ht1 : t ≤ (7/9)) :
    (109916026941/500000000000) + rest t + (0/1) ≤ 0 := by
  let u : ℝ := (t-(-1/1))/(16/9)
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ wholeNumerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound wholeNumerators wholeLeaves 0 0 1 0 whole_checked u
        (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using whole_endpoint
  have he := whole_identity u
  have hu : (-1/1)+(16/9)*u=t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [wholeDenominator])

def bandNumerators : List ℤ := [856800028540958978669543424, 61128206140841025663362425159680, -318258103386100956034903916544000, 372514902273690500568218941440000, 509329397985526033305694822400000, -1289591342670608519256398489600000, 584592618953733809853462528000000, 604772236828244618837352400000000, -941303399110680803431384000000000, 596358968961841341425572500000000, -228891614447001966791595000000000, 58412577978547845315576562500000, -10177757469129077045156250000000, 1201356367297614085107421875000, -92110956947434246582031250000, 4145759748939176971435546875, -83209023898275146484375000]

def bandDenominator : ℤ := 85680000000000000000000000000000

def bandLeaves : List (ℕ × ℕ × ℕ) := [(0, 3, 1), (1, 3, 1), (4, 4, 1), (5, 4, 1), (12, 5, 1), (26, 6, 1), (54, 7, 1), (110, 8, 1), (111, 8, 1), (112, 8, 1), (113, 8, 1), (57, 7, 1), (29, 6, 1), (15, 5, 1), (2, 2, 1), (6, 3, 1), (14, 4, 1), (30, 5, 1), (31, 5, 1)]

theorem band_checked : chainOK bandNumerators 0 0 bandLeaves 1 0 = true := by decide +kernel

theorem band_endpoint : 0 < evalZ bandNumerators 1 := by norm_num [bandNumerators, evalZ]

theorem band_identity (u : ℝ) :
    (109916026941/500000000000) + rest ((-4/5)+(1/4)*u) + (1/1) =
      -evalZ bandNumerators u / bandDenominator := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, bandNumerators, bandDenominator, evalZ]
  <;> ring

theorem band_sign (t : ℝ) (ht0 : (-4/5) ≤ t) (ht1 : t ≤ (-11/20)) :
    (109916026941/500000000000) + rest t + (1/1) ≤ 0 := by
  let u : ℝ := (t-(-4/5))/(1/4)
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ bandNumerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound bandNumerators bandLeaves 0 0 1 0 band_checked u
        (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using band_endpoint
  have he := band_identity u
  have hu : (-4/5)+(1/4)*u=t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [bandDenominator])

end

end D4Bound.ModerateGraphCertificate

