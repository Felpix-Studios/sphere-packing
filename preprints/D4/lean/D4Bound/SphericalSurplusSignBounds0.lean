-- Exact constants are tied to rays and scalar polynomial below.

import D4Bound.SphericalSurplusSignData0

import D4Bound.SphericalConcreteBasic

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign

open SphericalSign SphericalConcrete

def rawBound0 : ℚ := 130877701570004888847033217319318784541/148723869673221832089000000000000000000

def repairedBound0 : ℚ := 131430224020549714328939307470798784541/148723869673221832089000000000000000000

def maxCount0 : ℕ := 24

def repairDiagonal0 : ℚ := 133770012193/4999950000

theorem originNumerator0_exact : originNumerator rays0 = 4949969724295358919 := by
  decide +kernel

theorem rawBound0_correct : g0 1 + origin0 = (rawBound0:ℝ) := by
  unfold origin0
  rw [origin_eq, originNumerator0_exact]
  norm_num [g0,scalarPower0,scalarPowerDen0,evalZ,originDen0,countM0,
    v0,vNum0,b0,bNum0,rawBound0]

theorem repairedBound0_correct :
    (rawBound0:ℝ) + ((maxCount0:ℝ)-1) *
      ((eta0:ℝ) + (epsilon0:ℝ)*(repairDiagonal0:ℝ)) = (repairedBound0:ℝ) := by
  norm_num [rawBound0,maxCount0,eta0,epsilon0,repairDiagonal0,repairedBound0]

#print axioms rawBound0_correct

#print axioms repairedBound0_correct

end D4Bound.SphericalSurplusSign
