import D4Bound.SphericalCertS2Basic
import D4Bound.ScalarCheck

/-! Exact Legendre certificate for the graph's projected degree bound.
The polynomial has degree27. Its sign is checked on the entire closed interval
[-1,223/735], including its endpoint; no sampled inequalities are used. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
namespace ProjectedEightCertificate

def numerators : List ℤ := [13932824732782710534903556197107040364442695064347539101110406329245865345001220703125, -326132652359608649126246769438554969684240923636360968461071969808447957038879394531250, 7834151982689988292690893092564712961795257765993337355722751751396737337112426757812500, -223449420378962205739812971347950557215406929370823551586433252259638737916946411132812500, 5094328034504151490613279559934002595512461439285788519493787700841602433800697326660156250, -85797811313666236674835578115218311652056002678996714947652969074692460405796051025390625000, 1066484637211260631131981547938707127557347099258082728032412564641229218847115707397460937500, -9903524683310134875251455670549913691798436639875953328330348910685465614539677886962890625000, 69989905918863070234962047301755516486376946691417973047838652627611264624672288894653320312500, -383960730564293180930757362732759906466986107172400610812437006354133300537887432098388671875000, 1664667840876314205287338532644974223813476068313288940361366729454179207237490343139648437500000, -5789775901866622180959466846465616720048798984366982993401381628807310048227670581958007812500000, 16348631088588871112464405341207620972461682416763840502650939829791837887137105722816162109375000, -37825042929877094268456995997046291302077660130596088114285284881019049923130064460852050781250000, 72190423152607330944775016839049251431682506864020702481760871446429893770358578504245605468750000, -114166060413269816957351874307231268029954108517423724024971227858052313758379522839970937500000000, 149966675281152745950667087444178780684020053297853727103692447741613605154370812878407271484375000, -163678047032519238761182282529364063484319127936304235675442032076528448121105763681394449609375000, 148151519703313881219907580197832834410712678637974920901543257640344338946835507059598009765625000, -110725442426688384605102955127335021993520600184605327847066678913924376652877163069179124218750000, 67830255383728859935093410306984853065037531209687612131184003874535496369693158426569513565625000, -33680017963129120994010748078570256811820384787239770610521166549688373448482563406623177970000000, 13332833557304833848042271346805911580877656457097396795404660146529529654399295761795456403000000, -4106340595108866307377704033486382757378443117517105220348258304198426439603193465979979950000000, 947787173071754488122920746731281598450472287583384008199996240677091454016122573511195485625000, -154171316942832723527612799736050690966232579520828923273440041552881593055566243663783556936800, 15754728588446219668298941942998506185081296527373038180343848709507728546881053930251874411120, -760545728784654998348721913902371827931866065670111896032723963905689289388362291014426590368]

def denominator : ℤ := 10013642233556628887535789433117257015812180530018455377027392387390136718750000000000

def leaves : List (ℕ × ℕ × ℕ) := [(0, 5, 1), (1, 5, 1), (2, 5, 1), (3, 5, 1), (8, 6, 1), (18, 7, 1), (19, 7, 1), (20, 7, 1), (42, 8, 1), (43, 8, 1), (44, 8, 1), (90, 9, 1), (91, 9, 1), (184, 10, 1), (185, 10, 1), (186, 10, 1), (187, 10, 1), (47, 8, 1), (6, 5, 1), (7, 5, 1), (8, 5, 1), (9, 5, 1), (20, 6, 1), (42, 7, 1), (43, 7, 1), (88, 8, 1), (89, 8, 1), (90, 8, 1), (91, 8, 1), (23, 6, 1), (12, 5, 1), (26, 6, 1), (27, 6, 1), (112, 8, 1), (113, 8, 1), (57, 7, 1), (29, 6, 1), (15, 5, 1), (4, 3, 1), (5, 3, 1), (6, 3, 1), (14, 4, 1), (30, 5, 1), (62, 6, 1), (126, 7, 1), (127, 7, 1)]

theorem sign_check : chainOK numerators 0 0 leaves 1 0 = true := by decide +kernel

theorem endpoint_check : 0 < evalZ numerators 1 := by norm_num [numerators, evalZ]

noncomputable def coefficients : Fin 6 → ℝ := ![(14019856309/5000000000), (27945243689/10000000000), (19290997047/10000000000), (4096851867/10000000000), (39051053/1000000000), (4091477/1000000000)]

def degrees : Fin 6 → ℕ := ![1, 2, 3, 7, 17, 27]

noncomputable def rest (t : ℝ) : ℝ := ∑ i : Fin 6, coefficients i * Schoenberg2.legendre (degrees i) t

lemma P0 (t : ℝ) : Schoenberg2.legendre 0 t = ((1/1) + t * 0) := by

  simp <;> ring

lemma P1 (t : ℝ) : Schoenberg2.legendre 1 t = ((0/1) + t * ((1/1) + t * 0)) := by

  simp <;> ring

lemma P2 (t : ℝ) : Schoenberg2.legendre 2 t = ((-1/2) + t * ((0/1) + t * ((3/2) + t * 0))) := by

  rw [Schoenberg2.legendre_recurrence 0]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P1, P0]
  ring

lemma P3 (t : ℝ) : Schoenberg2.legendre 3 t = ((0/1) + t * ((-3/2) + t * ((0/1) + t * ((5/2) + t * 0)))) := by

  rw [Schoenberg2.legendre_recurrence 1]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P2, P1]
  ring

lemma P4 (t : ℝ) : Schoenberg2.legendre 4 t = ((3/8) + t * ((0/1) + t * ((-15/4) + t * ((0/1) + t * ((35/8) + t * 0))))) := by

  rw [Schoenberg2.legendre_recurrence 2]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P3, P2]
  ring

lemma P5 (t : ℝ) : Schoenberg2.legendre 5 t = ((0/1) + t * ((15/8) + t * ((0/1) + t * ((-35/4) + t * ((0/1) + t * ((63/8) + t * 0)))))) := by

  rw [Schoenberg2.legendre_recurrence 3]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P4, P3]
  ring

lemma P6 (t : ℝ) : Schoenberg2.legendre 6 t = ((-5/16) + t * ((0/1) + t * ((105/16) + t * ((0/1) + t * ((-315/16) + t * ((0/1) + t * ((231/16) + t * 0))))))) := by

  rw [Schoenberg2.legendre_recurrence 4]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P5, P4]
  ring

lemma P7 (t : ℝ) : Schoenberg2.legendre 7 t = ((0/1) + t * ((-35/16) + t * ((0/1) + t * ((315/16) + t * ((0/1) + t * ((-693/16) + t * ((0/1) + t * ((429/16) + t * 0)))))))) := by

  rw [Schoenberg2.legendre_recurrence 5]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P6, P5]
  ring

lemma P8 (t : ℝ) : Schoenberg2.legendre 8 t = ((35/128) + t * ((0/1) + t * ((-315/32) + t * ((0/1) + t * ((3465/64) + t * ((0/1) + t * ((-3003/32) + t * ((0/1) + t * ((6435/128) + t * 0))))))))) := by

  rw [Schoenberg2.legendre_recurrence 6]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P7, P6]
  ring

lemma P9 (t : ℝ) : Schoenberg2.legendre 9 t = ((0/1) + t * ((315/128) + t * ((0/1) + t * ((-1155/32) + t * ((0/1) + t * ((9009/64) + t * ((0/1) + t * ((-6435/32) + t * ((0/1) + t * ((12155/128) + t * 0)))))))))) := by

  rw [Schoenberg2.legendre_recurrence 7]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P8, P7]
  ring

lemma P10 (t : ℝ) : Schoenberg2.legendre 10 t = ((-63/256) + t * ((0/1) + t * ((3465/256) + t * ((0/1) + t * ((-15015/128) + t * ((0/1) + t * ((45045/128) + t * ((0/1) + t * ((-109395/256) + t * ((0/1) + t * ((46189/256) + t * 0))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 8]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P9, P8]
  ring

lemma P11 (t : ℝ) : Schoenberg2.legendre 11 t = ((0/1) + t * ((-693/256) + t * ((0/1) + t * ((15015/256) + t * ((0/1) + t * ((-45045/128) + t * ((0/1) + t * ((109395/128) + t * ((0/1) + t * ((-230945/256) + t * ((0/1) + t * ((88179/256) + t * 0)))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 9]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P10, P9]
  ring

lemma P12 (t : ℝ) : Schoenberg2.legendre 12 t = ((231/1024) + t * ((0/1) + t * ((-9009/512) + t * ((0/1) + t * ((225225/1024) + t * ((0/1) + t * ((-255255/256) + t * ((0/1) + t * ((2078505/1024) + t * ((0/1) + t * ((-969969/512) + t * ((0/1) + t * ((676039/1024) + t * 0))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 10]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P11, P10]
  ring

lemma P13 (t : ℝ) : Schoenberg2.legendre 13 t = ((0/1) + t * ((3003/1024) + t * ((0/1) + t * ((-45045/512) + t * ((0/1) + t * ((765765/1024) + t * ((0/1) + t * ((-692835/256) + t * ((0/1) + t * ((4849845/1024) + t * ((0/1) + t * ((-2028117/512) + t * ((0/1) + t * ((1300075/1024) + t * 0)))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 11]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P12, P11]
  ring

lemma P14 (t : ℝ) : Schoenberg2.legendre 14 t = ((-429/2048) + t * ((0/1) + t * ((45045/2048) + t * ((0/1) + t * ((-765765/2048) + t * ((0/1) + t * ((4849845/2048) + t * ((0/1) + t * ((-14549535/2048) + t * ((0/1) + t * ((22309287/2048) + t * ((0/1) + t * ((-16900975/2048) + t * ((0/1) + t * ((5014575/2048) + t * 0))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 12]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P13, P12]
  ring

lemma P15 (t : ℝ) : Schoenberg2.legendre 15 t = ((0/1) + t * ((-6435/2048) + t * ((0/1) + t * ((255255/2048) + t * ((0/1) + t * ((-2909907/2048) + t * ((0/1) + t * ((14549535/2048) + t * ((0/1) + t * ((-37182145/2048) + t * ((0/1) + t * ((50702925/2048) + t * ((0/1) + t * ((-35102025/2048) + t * ((0/1) + t * ((9694845/2048) + t * 0)))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 13]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P14, P13]
  ring

lemma P16 (t : ℝ) : Schoenberg2.legendre 16 t = ((6435/32768) + t * ((0/1) + t * ((-109395/4096) + t * ((0/1) + t * ((4849845/8192) + t * ((0/1) + t * ((-20369349/4096) + t * ((0/1) + t * ((334639305/16384) + t * ((0/1) + t * ((-185910725/4096) + t * ((0/1) + t * ((456326325/8192) + t * ((0/1) + t * ((-145422675/4096) + t * ((0/1) + t * ((300540195/32768) + t * 0))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 14]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P15, P14]
  ring

lemma P17 (t : ℝ) : Schoenberg2.legendre 17 t = ((0/1) + t * ((109395/32768) + t * ((0/1) + t * ((-692835/4096) + t * ((0/1) + t * ((20369349/8192) + t * ((0/1) + t * ((-66927861/4096) + t * ((0/1) + t * ((929553625/16384) + t * ((0/1) + t * ((-456326325/4096) + t * ((0/1) + t * ((1017958725/8192) + t * ((0/1) + t * ((-300540195/4096) + t * ((0/1) + t * ((583401555/32768) + t * 0)))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 15]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P16, P15]
  ring

lemma P18 (t : ℝ) : Schoenberg2.legendre 18 t = ((-12155/65536) + t * ((0/1) + t * ((2078505/65536) + t * ((0/1) + t * ((-14549535/16384) + t * ((0/1) + t * ((156165009/16384) + t * ((0/1) + t * ((-1673196525/32768) + t * ((0/1) + t * ((5019589575/32768) + t * ((0/1) + t * ((-4411154475/16384) + t * ((0/1) + t * ((4508102925/16384) + t * ((0/1) + t * ((-9917826435/65536) + t * ((0/1) + t * ((2268783825/65536) + t * 0))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 16]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P17, P16]
  ring

lemma P19 (t : ℝ) : Schoenberg2.legendre 19 t = ((0/1) + t * ((-230945/65536) + t * ((0/1) + t * ((14549535/65536) + t * ((0/1) + t * ((-66927861/16384) + t * ((0/1) + t * ((557732175/16384) + t * ((0/1) + t * ((-5019589575/32768) + t * ((0/1) + t * ((13233463425/32768) + t * ((0/1) + t * ((-10518906825/16384) + t * ((0/1) + t * ((9917826435/16384) + t * ((0/1) + t * ((-20419054425/65536) + t * ((0/1) + t * ((4418157975/65536) + t * 0)))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 17]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P18, P17]
  ring

lemma P20 (t : ℝ) : Schoenberg2.legendre 20 t = ((46189/262144) + t * ((0/1) + t * ((-4849845/131072) + t * ((0/1) + t * ((334639305/262144) + t * ((0/1) + t * ((-557732175/32768) + t * ((0/1) + t * ((15058768725/131072) + t * ((0/1) + t * ((-29113619535/65536) + t * ((0/1) + t * ((136745788725/131072) + t * ((0/1) + t * ((-49589132175/32768) + t * ((0/1) + t * ((347123925225/262144) + t * ((0/1) + t * ((-83945001525/131072) + t * ((0/1) + t * ((34461632205/262144) + t * 0))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 18]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P19, P18]
  ring

lemma P21 (t : ℝ) : Schoenberg2.legendre 21 t = ((0/1) + t * ((969969/262144) + t * ((0/1) + t * ((-37182145/131072) + t * ((0/1) + t * ((1673196525/262144) + t * ((0/1) + t * ((-2151252675/32768) + t * ((0/1) + t * ((48522699225/131072) + t * ((0/1) + t * ((-82047473235/65536) + t * ((0/1) + t * ((347123925225/131072) + t * ((0/1) + t * ((-115707975075/32768) + t * ((0/1) + t * ((755505013725/262144) + t * ((0/1) + t * ((-172308161025/131072) + t * ((0/1) + t * ((67282234305/262144) + t * 0)))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 19]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P20, P19]
  ring

lemma P22 (t : ℝ) : Schoenberg2.legendre 22 t = ((-88179/524288) + t * ((0/1) + t * ((22309287/524288) + t * ((0/1) + t * ((-929553625/524288) + t * ((0/1) + t * ((15058768725/524288) + t * ((0/1) + t * ((-62386327575/262144) + t * ((0/1) + t * ((300840735195/262144) + t * ((0/1) + t * ((-902522205585/262144) + t * ((0/1) + t * ((1735619626125/262144) + t * ((0/1) + t * ((-4281195077775/524288) + t * ((0/1) + t * ((3273855059475/524288) + t * ((0/1) + t * ((-1412926920405/524288) + t * ((0/1) + t * ((263012370465/524288) + t * 0))))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 20]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P21, P20]
  ring

lemma P23 (t : ℝ) : Schoenberg2.legendre 23 t = ((0/1) + t * ((-2028117/524288) + t * ((0/1) + t * ((185910725/524288) + t * ((0/1) + t * ((-5019589575/524288) + t * ((0/1) + t * ((62386327575/524288) + t * ((0/1) + t * ((-214886239425/262144) + t * ((0/1) + t * ((902522205585/262144) + t * ((0/1) + t * ((-2429867476575/262144) + t * ((0/1) + t * ((4281195077775/262144) + t * ((0/1) + t * ((-9821565178425/524288) + t * ((0/1) + t * ((7064634602025/524288) + t * ((0/1) + t * ((-2893136075115/524288) + t * ((0/1) + t * ((514589420475/524288) + t * 0)))))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 21]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P22, P21]
  ring

lemma P24 (t : ℝ) : Schoenberg2.legendre 24 t = ((676039/4194304) + t * ((0/1) + t * ((-50702925/1048576) + t * ((0/1) + t * ((5019589575/2097152) + t * ((0/1) + t * ((-48522699225/1048576) + t * ((0/1) + t * ((1933976154825/4194304) + t * ((0/1) + t * ((-1418249180205/524288) + t * ((0/1) + t * ((10529425731825/1048576) + t * ((0/1) + t * ((-12843585233325/524288) + t * ((0/1) + t * ((166966608033225/4194304) + t * ((0/1) + t * ((-44742685812825/1048576) + t * ((0/1) + t * ((60755857577415/2097152) + t * ((0/1) + t * ((-11835556670925/1048576) + t * ((0/1) + t * ((8061900920775/4194304) + t * 0))))))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 22]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P23, P22]
  ring

lemma P25 (t : ℝ) : Schoenberg2.legendre 25 t = ((0/1) + t * ((16900975/4194304) + t * ((0/1) + t * ((-456326325/1048576) + t * ((0/1) + t * ((29113619535/2097152) + t * ((0/1) + t * ((-214886239425/1048576) + t * ((0/1) + t * ((7091245901025/4194304) + t * ((0/1) + t * ((-4512611027925/524288) + t * ((0/1) + t * ((29968365544425/1048576) + t * ((0/1) + t * ((-33393321606645/524288) + t * ((0/1) + t * ((402684172315425/4194304) + t * ((0/1) + t * ((-101259762629025/1048576) + t * ((0/1) + t * ((130191123380175/2097152) + t * ((0/1) + t * ((-24185702762325/1048576) + t * ((0/1) + t * ((15801325804719/4194304) + t * 0)))))))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 23]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P24, P23]
  ring

lemma P26 (t : ℝ) : Schoenberg2.legendre 26 t = ((-1300075/8388608) + t * ((0/1) + t * ((456326325/8388608) + t * ((0/1) + t * ((-13233463425/4194304) + t * ((0/1) + t * ((300840735195/4194304) + t * ((0/1) + t * ((-7091245901025/8388608) + t * ((0/1) + t * ((49638721307175/8388608) + t * ((0/1) + t * ((-55655536011075/2097152) + t * ((0/1) + t * ((166966608033225/2097152) + t * ((0/1) + t * ((-1369126185872445/8388608) + t * ((0/1) + t * ((1923935489951475/8388608) + t * ((0/1) + t * ((-911337863661225/4194304) + t * ((0/1) + t * ((556271163533475/4194304) + t * ((0/1) + t * ((-395033145117975/8388608) + t * ((0/1) + t * ((61989816618513/8388608) + t * 0))))))))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 24]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P25, P24]
  ring

lemma P27 (t : ℝ) : Schoenberg2.legendre 27 t = ((0/1) + t * ((-35102025/8388608) + t * ((0/1) + t * ((4411154475/8388608) + t * ((0/1) + t * ((-82047473235/4194304) + t * ((0/1) + t * ((1418249180205/4194304) + t * ((0/1) + t * ((-27577067392875/8388608) + t * ((0/1) + t * ((166966608033225/8388608) + t * ((0/1) + t * ((-166966608033225/2097152) + t * ((0/1) + t * ((456375395290815/2097152) + t * ((0/1) + t * ((-3463083881912655/8388608) + t * ((0/1) + t * ((4556689318306125/8388608) + t * ((0/1) + t * ((-2039660932956075/4194304) + t * ((0/1) + t * ((1185099435353925/4194304) + t * ((0/1) + t * ((-805867616040669/8388608) + t * ((0/1) + t * ((121683714103007/8388608) + t * 0)))))))))))))))))))))))))))) := by

  rw [Schoenberg2.legendre_recurrence 25]

  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]

  rw [P26, P25]
  ring

theorem coefficients_nonneg (i : Fin 6) : 0 ≤ coefficients i := by
  fin_cases i <;> norm_num [coefficients]

theorem rest_energy : Sphere2EnergyNonneg rest := by
  exact sphere2Energy_sum Finset.univ coefficients degrees
    (fun i _ => coefficients_nonneg i)

theorem polynomial_identity (u : ℝ) :
    (99999/100000) + rest ((958*u-735)/735) = -evalZ numerators u / denominator := by
  norm_num [rest, coefficients, degrees, Fin.sum_univ_succ, P1, P2, P3, P7, P17, P27, numerators, denominator, evalZ]
  <;> ring

theorem sign (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 223/735) :
    (99999/100000) + rest t ≤ 0 := by
  let u : ℝ := (735*t+735)/958
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ numerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound numerators leaves 0 0 1 0 sign_check u (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using endpoint_check
  have he := polynomial_identity u
  have hu : (958*u-735)/735 = t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [denominator])

theorem diagonal : (99999/100000) + rest 1 = (89804130521/10000000000) := by
  norm_num [rest, coefficients, degrees, Fin.sum_univ_succ]

end ProjectedEightCertificate

/-- A sufficient replacement for the cited nine-point theorem at the precise
projected cutoff required by the broad antipodal graph. -/
theorem projected_eight_proved
    (C : Finset (EuclideanSpace ℝ (Fin 3))) (hC : ∀ u ∈ C, ‖u‖ = 1)
    (hsep : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ⟪u,v⟫ ≤ 223/735) : C.card ≤ 8 := by
  apply sphericalCodeBound3_of_energy (223/735) (99999/100000) (89804130521/10000000000) 8
    ProjectedEightCertificate.rest (by norm_num) (by norm_num)
    ProjectedEightCertificate.rest_energy ProjectedEightCertificate.diagonal
    ProjectedEightCertificate.sign C hC hsep

#print axioms projected_eight_proved
end D4Bound
