import D4Bound.SphericalCertBasic
import D4Bound.ScalarCheck

/-! Exact degree-20 annular Delsarte certificate, generated from the publication JSON.
Every coefficient identity, dyadic interval, and final objective is kernel checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
namespace AnnularCertificate

def numerators : List ℤ := [491655808401299259133395213234548715701117792031747, -48786869825274152044205108468157180477350207769384450, 2012059593867640748124780837876862859143829563868527800, -46060060282427733896964978127825951223946590936172450000, 665113291982847655600900948375205856625703932381776000000, -6506220545177201519626520524421182663838996224619577600000, 44986747062716166973287336365476300835957006003361696000000, -225151223863972661879661910242244342458355772266929216000000, 821577586239592177248610763549530810594807647743477760000000, -2153326991641757390339297536874163739061606106669158400000000, 3795928775552667742284962034893243878366844177418240000000000, -3323033221454633081887624014629126272905869247283200000000000, -3303805542710690746658512585177355635092148576665600000000000, 17525143301429314790506991830467905317820980555776000000000000, -33446704358996178369712459980475585364887967907840000000000000, 40548664229297482821579189559012444729159987200000000000000000, -33956686633555421366006017822744647004078080000000000000000000, 19718173034473620587619590592349825207534878720000000000000000, -7623360137635137904974625234348389101548339200000000000000000, 1770821760358011449773388885699342058651648000000000000000000, -187342121006517093679208195758410537369600000000000000000000]

def denominator : ℤ := 158348826079568435033375233347640128871000000000000

def leaves : List (ℕ × ℕ × ℕ) := [(0, 7, 1), (1, 7, 1), (4, 8, 1), (5, 8, 1), (6, 8, 1), (7, 8, 1), (16, 9, 1), (34, 10, 1), (35, 10, 1), (36, 10, 1), (74, 11, 1), (150, 12, 1), (302, 13, 1), (303, 13, 1), (608, 14, 1), (609, 14, 1), (610, 14, 1), (1222, 15, 1), (1223, 15, 1), (153, 12, 1), (77, 11, 1), (39, 10, 1), (5, 7, 1), (3, 6, 1), (4, 6, 1), (5, 6, 1), (12, 7, 1), (13, 7, 1), (28, 8, 1), (58, 9, 1), (59, 9, 1), (120, 10, 1), (121, 10, 1), (244, 11, 1), (245, 11, 1), (492, 12, 1), (493, 12, 1), (494, 12, 1), (495, 12, 1), (31, 8, 1), (4, 5, 1), (10, 6, 1), (11, 6, 1), (24, 7, 1), (50, 8, 1), (102, 9, 1), (206, 10, 1), (414, 11, 1), (415, 11, 1), (416, 11, 1), (417, 11, 1), (209, 10, 1), (105, 9, 1), (53, 8, 1), (27, 7, 1), (7, 5, 1), (8, 5, 1), (9, 5, 1), (20, 6, 1), (42, 7, 1), (86, 8, 1), (174, 9, 1), (175, 9, 1), (352, 10, 1), (353, 10, 1), (708, 11, 1), (709, 11, 1), (710, 11, 1), (711, 11, 1), (89, 8, 1), (45, 7, 1), (23, 6, 1), (12, 5, 1), (13, 5, 1), (28, 6, 1), (58, 7, 1), (118, 8, 1), (238, 9, 1), (478, 10, 1), (958, 11, 1), (959, 11, 1), (15, 5, 1), (8, 4, 1), (18, 5, 1), (76, 7, 1), (154, 8, 1), (155, 8, 1), (312, 9, 1), (313, 9, 1), (628, 10, 1), (1258, 11, 1), (1259, 11, 1), (1260, 11, 1), (1261, 11, 1), (631, 10, 1), (79, 7, 1), (10, 4, 1), (22, 5, 1), (46, 6, 1), (47, 6, 1), (96, 7, 1), (194, 8, 1), (780, 10, 1), (781, 10, 1), (1564, 11, 1), (1565, 11, 1), (1566, 11, 1), (3134, 12, 1), (3135, 12, 1), (49, 6, 1), (25, 5, 1), (26, 5, 1), (108, 7, 1), (218, 8, 1), (438, 9, 1), (878, 10, 1), (1758, 11, 1), (3518, 12, 1), (3519, 12, 1), (7040, 13, 1), (7041, 13, 1), (7042, 13, 1), (7043, 13, 1), (1761, 11, 1), (881, 10, 1), (441, 9, 1), (221, 8, 1), (111, 7, 1), (14, 4, 1), (30, 5, 1), (62, 6, 1), (126, 7, 1), (254, 8, 1), (255, 8, 1)]

theorem sign_check : chainOK numerators 0 0 leaves 1 0 = true := by decide +kernel

theorem endpoint_check : 0 < evalZ numerators 1 := by norm_num [numerators, evalZ]

noncomputable def coefficients : Fin 20 → ℝ := ![(1962104992391 / 1000000000000), (1645581560159 / 600000000000), (6711370694009 / 2000000000000), (359824748907 / 100000000000), (10744180850711 / 3000000000000), (884528309111 / 280000000000), (1293780988587 / 500000000000), (1631208597361 / 900000000000), (11539915221007 / 10000000000000), (6005937833447 / 11000000000000), (437794054693 / 2000000000000), (0 / 1), (0 / 1), (0 / 1), (603002303091 / 8000000000000), (1300943237023 / 17000000000000), (1618821107821 / 18000000000000), (242659809693 / 4750000000000), (623617611993 / 20000000000000), (62041370423 / 10500000000000)]

noncomputable def rest (t : ℝ) : ℝ := ∑ i : Fin 20, coefficients i * (Polynomial.Chebyshev.U ℝ (i.val + 1 : ℤ)).eval t

lemma U0 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (0 : ℤ)).eval t = (1 + t * 0) := by

  simp [Polynomial.Chebyshev.U_one] <;> ring

lemma U1 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (1 : ℤ)).eval t = (0 + t * (2 + t * 0)) := by

  simp [Polynomial.Chebyshev.U_one] <;> ring

lemma U2 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (2 : ℤ)).eval t = (-1 + t * (0 + t * (4 + t * 0))) := by

  rw [show (2 : ℤ) = 0 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U1, U0]
  ring

lemma U3 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (3 : ℤ)).eval t = (0 + t * (-4 + t * (0 + t * (8 + t * 0)))) := by

  rw [show (3 : ℤ) = 1 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U2, U1]
  ring

lemma U4 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (4 : ℤ)).eval t = (1 + t * (0 + t * (-12 + t * (0 + t * (16 + t * 0))))) := by

  rw [show (4 : ℤ) = 2 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U3, U2]
  ring

lemma U5 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (5 : ℤ)).eval t = (0 + t * (6 + t * (0 + t * (-32 + t * (0 + t * (32 + t * 0)))))) := by

  rw [show (5 : ℤ) = 3 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U4, U3]
  ring

lemma U6 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (6 : ℤ)).eval t = (-1 + t * (0 + t * (24 + t * (0 + t * (-80 + t * (0 + t * (64 + t * 0))))))) := by

  rw [show (6 : ℤ) = 4 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U5, U4]
  ring

lemma U7 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (7 : ℤ)).eval t = (0 + t * (-8 + t * (0 + t * (80 + t * (0 + t * (-192 + t * (0 + t * (128 + t * 0)))))))) := by

  rw [show (7 : ℤ) = 5 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U6, U5]
  ring

lemma U8 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (8 : ℤ)).eval t = (1 + t * (0 + t * (-40 + t * (0 + t * (240 + t * (0 + t * (-448 + t * (0 + t * (256 + t * 0))))))))) := by

  rw [show (8 : ℤ) = 6 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U7, U6]
  ring

lemma U9 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (9 : ℤ)).eval t = (0 + t * (10 + t * (0 + t * (-160 + t * (0 + t * (672 + t * (0 + t * (-1024 + t * (0 + t * (512 + t * 0)))))))))) := by

  rw [show (9 : ℤ) = 7 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U8, U7]
  ring

lemma U10 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (10 : ℤ)).eval t = (-1 + t * (0 + t * (60 + t * (0 + t * (-560 + t * (0 + t * (1792 + t * (0 + t * (-2304 + t * (0 + t * (1024 + t * 0))))))))))) := by

  rw [show (10 : ℤ) = 8 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U9, U8]
  ring

lemma U11 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (11 : ℤ)).eval t = (0 + t * (-12 + t * (0 + t * (280 + t * (0 + t * (-1792 + t * (0 + t * (4608 + t * (0 + t * (-5120 + t * (0 + t * (2048 + t * 0)))))))))))) := by

  rw [show (11 : ℤ) = 9 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U10, U9]
  ring

lemma U12 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (12 : ℤ)).eval t = (1 + t * (0 + t * (-84 + t * (0 + t * (1120 + t * (0 + t * (-5376 + t * (0 + t * (11520 + t * (0 + t * (-11264 + t * (0 + t * (4096 + t * 0))))))))))))) := by

  rw [show (12 : ℤ) = 10 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U11, U10]
  ring

lemma U13 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (13 : ℤ)).eval t = (0 + t * (14 + t * (0 + t * (-448 + t * (0 + t * (4032 + t * (0 + t * (-15360 + t * (0 + t * (28160 + t * (0 + t * (-24576 + t * (0 + t * (8192 + t * 0)))))))))))))) := by

  rw [show (13 : ℤ) = 11 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U12, U11]
  ring

lemma U14 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (14 : ℤ)).eval t = (-1 + t * (0 + t * (112 + t * (0 + t * (-2016 + t * (0 + t * (13440 + t * (0 + t * (-42240 + t * (0 + t * (67584 + t * (0 + t * (-53248 + t * (0 + t * (16384 + t * 0))))))))))))))) := by

  rw [show (14 : ℤ) = 12 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U13, U12]
  ring

lemma U15 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (15 : ℤ)).eval t = (0 + t * (-16 + t * (0 + t * (672 + t * (0 + t * (-8064 + t * (0 + t * (42240 + t * (0 + t * (-112640 + t * (0 + t * (159744 + t * (0 + t * (-114688 + t * (0 + t * (32768 + t * 0)))))))))))))))) := by

  rw [show (15 : ℤ) = 13 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U14, U13]
  ring

lemma U16 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (16 : ℤ)).eval t = (1 + t * (0 + t * (-144 + t * (0 + t * (3360 + t * (0 + t * (-29568 + t * (0 + t * (126720 + t * (0 + t * (-292864 + t * (0 + t * (372736 + t * (0 + t * (-245760 + t * (0 + t * (65536 + t * 0))))))))))))))))) := by

  rw [show (16 : ℤ) = 14 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U15, U14]
  ring

lemma U17 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (17 : ℤ)).eval t = (0 + t * (18 + t * (0 + t * (-960 + t * (0 + t * (14784 + t * (0 + t * (-101376 + t * (0 + t * (366080 + t * (0 + t * (-745472 + t * (0 + t * (860160 + t * (0 + t * (-524288 + t * (0 + t * (131072 + t * 0)))))))))))))))))) := by

  rw [show (17 : ℤ) = 15 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U16, U15]
  ring

lemma U18 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (18 : ℤ)).eval t = (-1 + t * (0 + t * (180 + t * (0 + t * (-5280 + t * (0 + t * (59136 + t * (0 + t * (-329472 + t * (0 + t * (1025024 + t * (0 + t * (-1863680 + t * (0 + t * (1966080 + t * (0 + t * (-1114112 + t * (0 + t * (262144 + t * 0))))))))))))))))))) := by

  rw [show (18 : ℤ) = 16 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U17, U16]
  ring

lemma U19 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (19 : ℤ)).eval t = (0 + t * (-20 + t * (0 + t * (1320 + t * (0 + t * (-25344 + t * (0 + t * (219648 + t * (0 + t * (-1025024 + t * (0 + t * (2795520 + t * (0 + t * (-4587520 + t * (0 + t * (4456448 + t * (0 + t * (-2359296 + t * (0 + t * (524288 + t * 0)))))))))))))))))))) := by

  rw [show (19 : ℤ) = 17 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U18, U17]
  ring

lemma U20 (t : ℝ) : (Polynomial.Chebyshev.U ℝ (20 : ℤ)).eval t = (1 + t * (0 + t * (-220 + t * (0 + t * (7920 + t * (0 + t * (-109824 + t * (0 + t * (768768 + t * (0 + t * (-3075072 + t * (0 + t * (7454720 + t * (0 + t * (-11141120 + t * (0 + t * (10027008 + t * (0 + t * (-4980736 + t * (0 + t * (1048576 + t * 0))))))))))))))))))))) := by

  rw [show (20 : ℤ) = 18 + 2 by norm_num, Polynomial.Chebyshev.U_add_two]

  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

  rw [U19, U18]
  ring

theorem coefficients_nonneg (i : Fin 20) : 0 ≤ coefficients i := by
  fin_cases i <;> norm_num [coefficients]

 theorem rest_energy : SphereEnergyNonneg rest := by
  exact sphereEnergy_sum Finset.univ coefficients (fun i : Fin 20 => i.val + 1)
    (fun i _ => coefficients_nonneg i)

theorem polynomial_identity (u : ℝ) :
    (999999 / 1000000) + rest ((90*u-49)/49) = -evalZ numerators u / denominator := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, U17, U18, U19, U20, numerators, denominator, evalZ]
  <;> ring

theorem sign (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 41/49) :
    (999999 / 1000000) + rest t ≤ 0 := by
  let u : ℝ := (49*t+49)/90
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ numerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound numerators leaves 0 0 1 0 sign_check u (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using endpoint_check
  have he := polynomial_identity u
  have hu : (90*u-49)/49 = t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [denominator])

 theorem diagonal : (999999 / 1000000) + rest 1 = (151196972764393 / 1000000000000) := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, Polynomial.Chebyshev.U_eval_one]

end AnnularCertificate

/-- The published annular code count, proved without a certificate hypothesis. -/
theorem annular_151_proved : SphericalCodeBound (41/49) 151 := by
  apply sphericalCodeBound_of_energy (41/49) (999999 / 1000000) (151196972764393 / 1000000000000) 151 AnnularCertificate.rest
  · norm_num
  · norm_num
  · exact AnnularCertificate.rest_energy
  · exact AnnularCertificate.diagonal
  · exact AnnularCertificate.sign

#print axioms annular_151_proved
end D4Bound
