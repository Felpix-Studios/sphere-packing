import D4Bound.SphericalSurplusSignTransform1XData

import D4Bound.SphericalSurplusSignTransform1Y

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem transform1X_c12_r0 : ∀ k,
    matrixX affine1 transform1Y 0 12 k = scaleTensor transformFactor1X transform1X 0 12 k := by decide +kernel

theorem transform1X_c12_r1 : ∀ k,
    matrixX affine1 transform1Y 1 12 k = scaleTensor transformFactor1X transform1X 1 12 k := by decide +kernel

theorem transform1X_c12_r2 : ∀ k,
    matrixX affine1 transform1Y 2 12 k = scaleTensor transformFactor1X transform1X 2 12 k := by decide +kernel

theorem transform1X_c12_r3 : ∀ k,
    matrixX affine1 transform1Y 3 12 k = scaleTensor transformFactor1X transform1X 3 12 k := by decide +kernel

theorem transform1X_c12_r4 : ∀ k,
    matrixX affine1 transform1Y 4 12 k = scaleTensor transformFactor1X transform1X 4 12 k := by decide +kernel

theorem transform1X_c12_r5 : ∀ k,
    matrixX affine1 transform1Y 5 12 k = scaleTensor transformFactor1X transform1X 5 12 k := by decide +kernel

theorem transform1X_c12_r6 : ∀ k,
    matrixX affine1 transform1Y 6 12 k = scaleTensor transformFactor1X transform1X 6 12 k := by decide +kernel

theorem transform1X_c12_r7 : ∀ k,
    matrixX affine1 transform1Y 7 12 k = scaleTensor transformFactor1X transform1X 7 12 k := by decide +kernel

theorem transform1X_c12_r8 : ∀ k,
    matrixX affine1 transform1Y 8 12 k = scaleTensor transformFactor1X transform1X 8 12 k := by decide +kernel

theorem transform1X_c12_r9 : ∀ k,
    matrixX affine1 transform1Y 9 12 k = scaleTensor transformFactor1X transform1X 9 12 k := by decide +kernel

theorem transform1X_c12_r10 : ∀ k,
    matrixX affine1 transform1Y 10 12 k = scaleTensor transformFactor1X transform1X 10 12 k := by decide +kernel

theorem transform1X_c12_r11 : ∀ k,
    matrixX affine1 transform1Y 11 12 k = scaleTensor transformFactor1X transform1X 11 12 k := by decide +kernel

theorem transform1X_c12_r12 : ∀ k,
    matrixX affine1 transform1Y 12 12 k = scaleTensor transformFactor1X transform1X 12 12 k := by decide +kernel

theorem transform1X_c12_r13 : ∀ k,
    matrixX affine1 transform1Y 13 12 k = scaleTensor transformFactor1X transform1X 13 12 k := by decide +kernel

theorem transform1X_c12_r14 : ∀ k,
    matrixX affine1 transform1Y 14 12 k = scaleTensor transformFactor1X transform1X 14 12 k := by decide +kernel

theorem transform1X_c12_r15 : ∀ k,
    matrixX affine1 transform1Y 15 12 k = scaleTensor transformFactor1X transform1X 15 12 k := by decide +kernel

theorem transform1X_c12_r16 : ∀ k,
    matrixX affine1 transform1Y 16 12 k = scaleTensor transformFactor1X transform1X 16 12 k := by decide +kernel

theorem transform1X_col12 : ∀ i k,
    matrixX affine1 transform1Y i 12 k = scaleTensor transformFactor1X transform1X i 12 k := by
  intro i k
  fin_cases i
  · exact transform1X_c12_r0 k
  · exact transform1X_c12_r1 k
  · exact transform1X_c12_r2 k
  · exact transform1X_c12_r3 k
  · exact transform1X_c12_r4 k
  · exact transform1X_c12_r5 k
  · exact transform1X_c12_r6 k
  · exact transform1X_c12_r7 k
  · exact transform1X_c12_r8 k
  · exact transform1X_c12_r9 k
  · exact transform1X_c12_r10 k
  · exact transform1X_c12_r11 k
  · exact transform1X_c12_r12 k
  · exact transform1X_c12_r13 k
  · exact transform1X_c12_r14 k
  · exact transform1X_c12_r15 k
  · exact transform1X_c12_r16 k

theorem transform1X_c13_r0 : ∀ k,
    matrixX affine1 transform1Y 0 13 k = scaleTensor transformFactor1X transform1X 0 13 k := by decide +kernel

theorem transform1X_c13_r1 : ∀ k,
    matrixX affine1 transform1Y 1 13 k = scaleTensor transformFactor1X transform1X 1 13 k := by decide +kernel

theorem transform1X_c13_r2 : ∀ k,
    matrixX affine1 transform1Y 2 13 k = scaleTensor transformFactor1X transform1X 2 13 k := by decide +kernel

theorem transform1X_c13_r3 : ∀ k,
    matrixX affine1 transform1Y 3 13 k = scaleTensor transformFactor1X transform1X 3 13 k := by decide +kernel

theorem transform1X_c13_r4 : ∀ k,
    matrixX affine1 transform1Y 4 13 k = scaleTensor transformFactor1X transform1X 4 13 k := by decide +kernel

theorem transform1X_c13_r5 : ∀ k,
    matrixX affine1 transform1Y 5 13 k = scaleTensor transformFactor1X transform1X 5 13 k := by decide +kernel

theorem transform1X_c13_r6 : ∀ k,
    matrixX affine1 transform1Y 6 13 k = scaleTensor transformFactor1X transform1X 6 13 k := by decide +kernel

theorem transform1X_c13_r7 : ∀ k,
    matrixX affine1 transform1Y 7 13 k = scaleTensor transformFactor1X transform1X 7 13 k := by decide +kernel

theorem transform1X_c13_r8 : ∀ k,
    matrixX affine1 transform1Y 8 13 k = scaleTensor transformFactor1X transform1X 8 13 k := by decide +kernel

theorem transform1X_c13_r9 : ∀ k,
    matrixX affine1 transform1Y 9 13 k = scaleTensor transformFactor1X transform1X 9 13 k := by decide +kernel

theorem transform1X_c13_r10 : ∀ k,
    matrixX affine1 transform1Y 10 13 k = scaleTensor transformFactor1X transform1X 10 13 k := by decide +kernel

theorem transform1X_c13_r11 : ∀ k,
    matrixX affine1 transform1Y 11 13 k = scaleTensor transformFactor1X transform1X 11 13 k := by decide +kernel

theorem transform1X_c13_r12 : ∀ k,
    matrixX affine1 transform1Y 12 13 k = scaleTensor transformFactor1X transform1X 12 13 k := by decide +kernel

theorem transform1X_c13_r13 : ∀ k,
    matrixX affine1 transform1Y 13 13 k = scaleTensor transformFactor1X transform1X 13 13 k := by decide +kernel

theorem transform1X_c13_r14 : ∀ k,
    matrixX affine1 transform1Y 14 13 k = scaleTensor transformFactor1X transform1X 14 13 k := by decide +kernel

theorem transform1X_c13_r15 : ∀ k,
    matrixX affine1 transform1Y 15 13 k = scaleTensor transformFactor1X transform1X 15 13 k := by decide +kernel

theorem transform1X_c13_r16 : ∀ k,
    matrixX affine1 transform1Y 16 13 k = scaleTensor transformFactor1X transform1X 16 13 k := by decide +kernel

theorem transform1X_col13 : ∀ i k,
    matrixX affine1 transform1Y i 13 k = scaleTensor transformFactor1X transform1X i 13 k := by
  intro i k
  fin_cases i
  · exact transform1X_c13_r0 k
  · exact transform1X_c13_r1 k
  · exact transform1X_c13_r2 k
  · exact transform1X_c13_r3 k
  · exact transform1X_c13_r4 k
  · exact transform1X_c13_r5 k
  · exact transform1X_c13_r6 k
  · exact transform1X_c13_r7 k
  · exact transform1X_c13_r8 k
  · exact transform1X_c13_r9 k
  · exact transform1X_c13_r10 k
  · exact transform1X_c13_r11 k
  · exact transform1X_c13_r12 k
  · exact transform1X_c13_r13 k
  · exact transform1X_c13_r14 k
  · exact transform1X_c13_r15 k
  · exact transform1X_c13_r16 k

theorem transform1X_c14_r0 : ∀ k,
    matrixX affine1 transform1Y 0 14 k = scaleTensor transformFactor1X transform1X 0 14 k := by decide +kernel

theorem transform1X_c14_r1 : ∀ k,
    matrixX affine1 transform1Y 1 14 k = scaleTensor transformFactor1X transform1X 1 14 k := by decide +kernel

theorem transform1X_c14_r2 : ∀ k,
    matrixX affine1 transform1Y 2 14 k = scaleTensor transformFactor1X transform1X 2 14 k := by decide +kernel

theorem transform1X_c14_r3 : ∀ k,
    matrixX affine1 transform1Y 3 14 k = scaleTensor transformFactor1X transform1X 3 14 k := by decide +kernel

theorem transform1X_c14_r4 : ∀ k,
    matrixX affine1 transform1Y 4 14 k = scaleTensor transformFactor1X transform1X 4 14 k := by decide +kernel

theorem transform1X_c14_r5 : ∀ k,
    matrixX affine1 transform1Y 5 14 k = scaleTensor transformFactor1X transform1X 5 14 k := by decide +kernel

theorem transform1X_c14_r6 : ∀ k,
    matrixX affine1 transform1Y 6 14 k = scaleTensor transformFactor1X transform1X 6 14 k := by decide +kernel

theorem transform1X_c14_r7 : ∀ k,
    matrixX affine1 transform1Y 7 14 k = scaleTensor transformFactor1X transform1X 7 14 k := by decide +kernel

theorem transform1X_c14_r8 : ∀ k,
    matrixX affine1 transform1Y 8 14 k = scaleTensor transformFactor1X transform1X 8 14 k := by decide +kernel

theorem transform1X_c14_r9 : ∀ k,
    matrixX affine1 transform1Y 9 14 k = scaleTensor transformFactor1X transform1X 9 14 k := by decide +kernel

theorem transform1X_c14_r10 : ∀ k,
    matrixX affine1 transform1Y 10 14 k = scaleTensor transformFactor1X transform1X 10 14 k := by decide +kernel

theorem transform1X_c14_r11 : ∀ k,
    matrixX affine1 transform1Y 11 14 k = scaleTensor transformFactor1X transform1X 11 14 k := by decide +kernel

theorem transform1X_c14_r12 : ∀ k,
    matrixX affine1 transform1Y 12 14 k = scaleTensor transformFactor1X transform1X 12 14 k := by decide +kernel

theorem transform1X_c14_r13 : ∀ k,
    matrixX affine1 transform1Y 13 14 k = scaleTensor transformFactor1X transform1X 13 14 k := by decide +kernel

theorem transform1X_c14_r14 : ∀ k,
    matrixX affine1 transform1Y 14 14 k = scaleTensor transformFactor1X transform1X 14 14 k := by decide +kernel

theorem transform1X_c14_r15 : ∀ k,
    matrixX affine1 transform1Y 15 14 k = scaleTensor transformFactor1X transform1X 15 14 k := by decide +kernel

theorem transform1X_c14_r16 : ∀ k,
    matrixX affine1 transform1Y 16 14 k = scaleTensor transformFactor1X transform1X 16 14 k := by decide +kernel

theorem transform1X_col14 : ∀ i k,
    matrixX affine1 transform1Y i 14 k = scaleTensor transformFactor1X transform1X i 14 k := by
  intro i k
  fin_cases i
  · exact transform1X_c14_r0 k
  · exact transform1X_c14_r1 k
  · exact transform1X_c14_r2 k
  · exact transform1X_c14_r3 k
  · exact transform1X_c14_r4 k
  · exact transform1X_c14_r5 k
  · exact transform1X_c14_r6 k
  · exact transform1X_c14_r7 k
  · exact transform1X_c14_r8 k
  · exact transform1X_c14_r9 k
  · exact transform1X_c14_r10 k
  · exact transform1X_c14_r11 k
  · exact transform1X_c14_r12 k
  · exact transform1X_c14_r13 k
  · exact transform1X_c14_r14 k
  · exact transform1X_c14_r15 k
  · exact transform1X_c14_r16 k

theorem transform1X_c15_r0 : ∀ k,
    matrixX affine1 transform1Y 0 15 k = scaleTensor transformFactor1X transform1X 0 15 k := by decide +kernel

theorem transform1X_c15_r1 : ∀ k,
    matrixX affine1 transform1Y 1 15 k = scaleTensor transformFactor1X transform1X 1 15 k := by decide +kernel

theorem transform1X_c15_r2 : ∀ k,
    matrixX affine1 transform1Y 2 15 k = scaleTensor transformFactor1X transform1X 2 15 k := by decide +kernel

theorem transform1X_c15_r3 : ∀ k,
    matrixX affine1 transform1Y 3 15 k = scaleTensor transformFactor1X transform1X 3 15 k := by decide +kernel

theorem transform1X_c15_r4 : ∀ k,
    matrixX affine1 transform1Y 4 15 k = scaleTensor transformFactor1X transform1X 4 15 k := by decide +kernel

theorem transform1X_c15_r5 : ∀ k,
    matrixX affine1 transform1Y 5 15 k = scaleTensor transformFactor1X transform1X 5 15 k := by decide +kernel

theorem transform1X_c15_r6 : ∀ k,
    matrixX affine1 transform1Y 6 15 k = scaleTensor transformFactor1X transform1X 6 15 k := by decide +kernel

theorem transform1X_c15_r7 : ∀ k,
    matrixX affine1 transform1Y 7 15 k = scaleTensor transformFactor1X transform1X 7 15 k := by decide +kernel

theorem transform1X_c15_r8 : ∀ k,
    matrixX affine1 transform1Y 8 15 k = scaleTensor transformFactor1X transform1X 8 15 k := by decide +kernel

theorem transform1X_c15_r9 : ∀ k,
    matrixX affine1 transform1Y 9 15 k = scaleTensor transformFactor1X transform1X 9 15 k := by decide +kernel

theorem transform1X_c15_r10 : ∀ k,
    matrixX affine1 transform1Y 10 15 k = scaleTensor transformFactor1X transform1X 10 15 k := by decide +kernel

theorem transform1X_c15_r11 : ∀ k,
    matrixX affine1 transform1Y 11 15 k = scaleTensor transformFactor1X transform1X 11 15 k := by decide +kernel

theorem transform1X_c15_r12 : ∀ k,
    matrixX affine1 transform1Y 12 15 k = scaleTensor transformFactor1X transform1X 12 15 k := by decide +kernel

theorem transform1X_c15_r13 : ∀ k,
    matrixX affine1 transform1Y 13 15 k = scaleTensor transformFactor1X transform1X 13 15 k := by decide +kernel

theorem transform1X_c15_r14 : ∀ k,
    matrixX affine1 transform1Y 14 15 k = scaleTensor transformFactor1X transform1X 14 15 k := by decide +kernel

theorem transform1X_c15_r15 : ∀ k,
    matrixX affine1 transform1Y 15 15 k = scaleTensor transformFactor1X transform1X 15 15 k := by decide +kernel

theorem transform1X_c15_r16 : ∀ k,
    matrixX affine1 transform1Y 16 15 k = scaleTensor transformFactor1X transform1X 16 15 k := by decide +kernel

theorem transform1X_col15 : ∀ i k,
    matrixX affine1 transform1Y i 15 k = scaleTensor transformFactor1X transform1X i 15 k := by
  intro i k
  fin_cases i
  · exact transform1X_c15_r0 k
  · exact transform1X_c15_r1 k
  · exact transform1X_c15_r2 k
  · exact transform1X_c15_r3 k
  · exact transform1X_c15_r4 k
  · exact transform1X_c15_r5 k
  · exact transform1X_c15_r6 k
  · exact transform1X_c15_r7 k
  · exact transform1X_c15_r8 k
  · exact transform1X_c15_r9 k
  · exact transform1X_c15_r10 k
  · exact transform1X_c15_r11 k
  · exact transform1X_c15_r12 k
  · exact transform1X_c15_r13 k
  · exact transform1X_c15_r14 k
  · exact transform1X_c15_r15 k
  · exact transform1X_c15_r16 k

theorem transform1X_c16_r0 : ∀ k,
    matrixX affine1 transform1Y 0 16 k = scaleTensor transformFactor1X transform1X 0 16 k := by decide +kernel

theorem transform1X_c16_r1 : ∀ k,
    matrixX affine1 transform1Y 1 16 k = scaleTensor transformFactor1X transform1X 1 16 k := by decide +kernel

theorem transform1X_c16_r2 : ∀ k,
    matrixX affine1 transform1Y 2 16 k = scaleTensor transformFactor1X transform1X 2 16 k := by decide +kernel

theorem transform1X_c16_r3 : ∀ k,
    matrixX affine1 transform1Y 3 16 k = scaleTensor transformFactor1X transform1X 3 16 k := by decide +kernel

theorem transform1X_c16_r4 : ∀ k,
    matrixX affine1 transform1Y 4 16 k = scaleTensor transformFactor1X transform1X 4 16 k := by decide +kernel

theorem transform1X_c16_r5 : ∀ k,
    matrixX affine1 transform1Y 5 16 k = scaleTensor transformFactor1X transform1X 5 16 k := by decide +kernel

theorem transform1X_c16_r6 : ∀ k,
    matrixX affine1 transform1Y 6 16 k = scaleTensor transformFactor1X transform1X 6 16 k := by decide +kernel

theorem transform1X_c16_r7 : ∀ k,
    matrixX affine1 transform1Y 7 16 k = scaleTensor transformFactor1X transform1X 7 16 k := by decide +kernel

theorem transform1X_c16_r8 : ∀ k,
    matrixX affine1 transform1Y 8 16 k = scaleTensor transformFactor1X transform1X 8 16 k := by decide +kernel

theorem transform1X_c16_r9 : ∀ k,
    matrixX affine1 transform1Y 9 16 k = scaleTensor transformFactor1X transform1X 9 16 k := by decide +kernel

theorem transform1X_c16_r10 : ∀ k,
    matrixX affine1 transform1Y 10 16 k = scaleTensor transformFactor1X transform1X 10 16 k := by decide +kernel

theorem transform1X_c16_r11 : ∀ k,
    matrixX affine1 transform1Y 11 16 k = scaleTensor transformFactor1X transform1X 11 16 k := by decide +kernel

theorem transform1X_c16_r12 : ∀ k,
    matrixX affine1 transform1Y 12 16 k = scaleTensor transformFactor1X transform1X 12 16 k := by decide +kernel

theorem transform1X_c16_r13 : ∀ k,
    matrixX affine1 transform1Y 13 16 k = scaleTensor transformFactor1X transform1X 13 16 k := by decide +kernel

theorem transform1X_c16_r14 : ∀ k,
    matrixX affine1 transform1Y 14 16 k = scaleTensor transformFactor1X transform1X 14 16 k := by decide +kernel

theorem transform1X_c16_r15 : ∀ k,
    matrixX affine1 transform1Y 15 16 k = scaleTensor transformFactor1X transform1X 15 16 k := by decide +kernel

theorem transform1X_c16_r16 : ∀ k,
    matrixX affine1 transform1Y 16 16 k = scaleTensor transformFactor1X transform1X 16 16 k := by decide +kernel

theorem transform1X_col16 : ∀ i k,
    matrixX affine1 transform1Y i 16 k = scaleTensor transformFactor1X transform1X i 16 k := by
  intro i k
  fin_cases i
  · exact transform1X_c16_r0 k
  · exact transform1X_c16_r1 k
  · exact transform1X_c16_r2 k
  · exact transform1X_c16_r3 k
  · exact transform1X_c16_r4 k
  · exact transform1X_c16_r5 k
  · exact transform1X_c16_r6 k
  · exact transform1X_c16_r7 k
  · exact transform1X_c16_r8 k
  · exact transform1X_c16_r9 k
  · exact transform1X_c16_r10 k
  · exact transform1X_c16_r11 k
  · exact transform1X_c16_r12 k
  · exact transform1X_c16_r13 k
  · exact transform1X_c16_r14 k
  · exact transform1X_c16_r15 k
  · exact transform1X_c16_r16 k

#print axioms transform1X_col12

end D4Bound.SphericalSurplusSign.Bernstein16
