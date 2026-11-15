import D4Bound.CensusData

namespace D4Bound.CensusArithmetic

def quadratic (c : Array ℤ) (v : Counts) : ℤ :=
  let a : ℤ := v.n0
  let b : ℤ := v.n1
  let d : ℤ := v.n2
  let e : ℤ := v.n3
  let f : ℤ := v.n4
  c[0]! + 2 * (c[1]!*a+c[2]!*b+c[3]!*d+c[4]!*e+c[5]!*f) +
  c[6]!*a*a + 2*c[7]!*a*b + 2*c[8]!*a*d + 2*c[9]!*a*e + 2*c[10]!*a*f +
  c[11]!*b*b + 2*c[12]!*b*d + 2*c[13]!*b*e + 2*c[14]!*b*f +
  c[15]!*d*d + 2*c[16]!*d*e + 2*c[17]!*d*f +
  c[18]!*e*e + 2*c[19]!*e*f + c[20]!*f*f

def affine (c : Array ℤ) (v : Counts) : ℤ :=
  c[0]!+c[1]!*v.n0+c[2]!*v.n1+c[3]!*v.n2+c[4]!*v.n3+c[5]!*v.n4

def numerator (v : Counts) : ℤ :=
  let cv := quadratic countCoeffs v
  let radial := planeCoeffs.foldl (fun acc c => max acc (cv + affine c v))
    (quadratic totalCoeffs v)
  radial + surplusNumerators[5*v.n4+first v-1]!

def test (v : Counts) : Bool :=
  decide (floorNumerators[5*v.n4+first v-1]! ≤ numerator v)

def floorDataOK : Bool := groups.all fun g =>
  decide ((floorNumerators[5*g.1+g.2.1-1]! : ℚ) / (denominator : ℚ) = g.2.2)

def lower (v : Counts) : ℚ := (numerator v : ℚ) / (denominator : ℚ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem denominator_pos : (0 : ℚ) < denominator := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floor_data_checked : floorDataOK = true := by decide +kernel

theorem test_sound {v : Counts} (h : test v = true)
    {g : ℕ × ℕ × ℚ} (hg : g ∈ groups)
    (hN : g.1 = v.n4) (hj : g.2.1 = first v) : g.2.2 ≤ lower v := by
  have hf := (List.all_eq_true.mp floor_data_checked) g hg
  have heq : (floorNumerators[5*g.1+g.2.1-1]! : ℚ) / (denominator : ℚ) = g.2.2 := by
    simpa using hf
  have hi : floorNumerators[5*v.n4+first v-1]! ≤ numerator v := by simpa [test] using h
  rw [← heq, hN, hj]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hi) denominator_pos.le

-- A malformed certificate is rejected even on the singleton zero-count domain.
example : allAt 0 (fun _ => false) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem census_N0 : allAt 0 test = true := by decide +kernel

end D4Bound.CensusArithmetic
