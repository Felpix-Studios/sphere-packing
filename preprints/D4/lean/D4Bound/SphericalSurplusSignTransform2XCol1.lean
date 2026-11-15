import D4Bound.SphericalSurplusSignTransform2XData

import D4Bound.SphericalSurplusSignTransform2Y

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem transform2X_c6_r0 : ∀ k,
    matrixX affine2 transform2Y 0 6 k = scaleTensor transformFactor2X transform2X 0 6 k := by decide +kernel

theorem transform2X_c6_r1 : ∀ k,
    matrixX affine2 transform2Y 1 6 k = scaleTensor transformFactor2X transform2X 1 6 k := by decide +kernel

theorem transform2X_c6_r2 : ∀ k,
    matrixX affine2 transform2Y 2 6 k = scaleTensor transformFactor2X transform2X 2 6 k := by decide +kernel

theorem transform2X_c6_r3 : ∀ k,
    matrixX affine2 transform2Y 3 6 k = scaleTensor transformFactor2X transform2X 3 6 k := by decide +kernel

theorem transform2X_c6_r4 : ∀ k,
    matrixX affine2 transform2Y 4 6 k = scaleTensor transformFactor2X transform2X 4 6 k := by decide +kernel

theorem transform2X_c6_r5 : ∀ k,
    matrixX affine2 transform2Y 5 6 k = scaleTensor transformFactor2X transform2X 5 6 k := by decide +kernel

theorem transform2X_c6_r6 : ∀ k,
    matrixX affine2 transform2Y 6 6 k = scaleTensor transformFactor2X transform2X 6 6 k := by decide +kernel

theorem transform2X_c6_r7 : ∀ k,
    matrixX affine2 transform2Y 7 6 k = scaleTensor transformFactor2X transform2X 7 6 k := by decide +kernel

theorem transform2X_c6_r8 : ∀ k,
    matrixX affine2 transform2Y 8 6 k = scaleTensor transformFactor2X transform2X 8 6 k := by decide +kernel

theorem transform2X_c6_r9 : ∀ k,
    matrixX affine2 transform2Y 9 6 k = scaleTensor transformFactor2X transform2X 9 6 k := by decide +kernel

theorem transform2X_c6_r10 : ∀ k,
    matrixX affine2 transform2Y 10 6 k = scaleTensor transformFactor2X transform2X 10 6 k := by decide +kernel

theorem transform2X_c6_r11 : ∀ k,
    matrixX affine2 transform2Y 11 6 k = scaleTensor transformFactor2X transform2X 11 6 k := by decide +kernel

theorem transform2X_c6_r12 : ∀ k,
    matrixX affine2 transform2Y 12 6 k = scaleTensor transformFactor2X transform2X 12 6 k := by decide +kernel

theorem transform2X_c6_r13 : ∀ k,
    matrixX affine2 transform2Y 13 6 k = scaleTensor transformFactor2X transform2X 13 6 k := by decide +kernel

theorem transform2X_c6_r14 : ∀ k,
    matrixX affine2 transform2Y 14 6 k = scaleTensor transformFactor2X transform2X 14 6 k := by decide +kernel

theorem transform2X_c6_r15 : ∀ k,
    matrixX affine2 transform2Y 15 6 k = scaleTensor transformFactor2X transform2X 15 6 k := by decide +kernel

theorem transform2X_c6_r16 : ∀ k,
    matrixX affine2 transform2Y 16 6 k = scaleTensor transformFactor2X transform2X 16 6 k := by decide +kernel

theorem transform2X_col6 : ∀ i k,
    matrixX affine2 transform2Y i 6 k = scaleTensor transformFactor2X transform2X i 6 k := by
  intro i k
  fin_cases i
  · exact transform2X_c6_r0 k
  · exact transform2X_c6_r1 k
  · exact transform2X_c6_r2 k
  · exact transform2X_c6_r3 k
  · exact transform2X_c6_r4 k
  · exact transform2X_c6_r5 k
  · exact transform2X_c6_r6 k
  · exact transform2X_c6_r7 k
  · exact transform2X_c6_r8 k
  · exact transform2X_c6_r9 k
  · exact transform2X_c6_r10 k
  · exact transform2X_c6_r11 k
  · exact transform2X_c6_r12 k
  · exact transform2X_c6_r13 k
  · exact transform2X_c6_r14 k
  · exact transform2X_c6_r15 k
  · exact transform2X_c6_r16 k

theorem transform2X_c7_r0 : ∀ k,
    matrixX affine2 transform2Y 0 7 k = scaleTensor transformFactor2X transform2X 0 7 k := by decide +kernel

theorem transform2X_c7_r1 : ∀ k,
    matrixX affine2 transform2Y 1 7 k = scaleTensor transformFactor2X transform2X 1 7 k := by decide +kernel

theorem transform2X_c7_r2 : ∀ k,
    matrixX affine2 transform2Y 2 7 k = scaleTensor transformFactor2X transform2X 2 7 k := by decide +kernel

theorem transform2X_c7_r3 : ∀ k,
    matrixX affine2 transform2Y 3 7 k = scaleTensor transformFactor2X transform2X 3 7 k := by decide +kernel

theorem transform2X_c7_r4 : ∀ k,
    matrixX affine2 transform2Y 4 7 k = scaleTensor transformFactor2X transform2X 4 7 k := by decide +kernel

theorem transform2X_c7_r5 : ∀ k,
    matrixX affine2 transform2Y 5 7 k = scaleTensor transformFactor2X transform2X 5 7 k := by decide +kernel

theorem transform2X_c7_r6 : ∀ k,
    matrixX affine2 transform2Y 6 7 k = scaleTensor transformFactor2X transform2X 6 7 k := by decide +kernel

theorem transform2X_c7_r7 : ∀ k,
    matrixX affine2 transform2Y 7 7 k = scaleTensor transformFactor2X transform2X 7 7 k := by decide +kernel

theorem transform2X_c7_r8 : ∀ k,
    matrixX affine2 transform2Y 8 7 k = scaleTensor transformFactor2X transform2X 8 7 k := by decide +kernel

theorem transform2X_c7_r9 : ∀ k,
    matrixX affine2 transform2Y 9 7 k = scaleTensor transformFactor2X transform2X 9 7 k := by decide +kernel

theorem transform2X_c7_r10 : ∀ k,
    matrixX affine2 transform2Y 10 7 k = scaleTensor transformFactor2X transform2X 10 7 k := by decide +kernel

theorem transform2X_c7_r11 : ∀ k,
    matrixX affine2 transform2Y 11 7 k = scaleTensor transformFactor2X transform2X 11 7 k := by decide +kernel

theorem transform2X_c7_r12 : ∀ k,
    matrixX affine2 transform2Y 12 7 k = scaleTensor transformFactor2X transform2X 12 7 k := by decide +kernel

theorem transform2X_c7_r13 : ∀ k,
    matrixX affine2 transform2Y 13 7 k = scaleTensor transformFactor2X transform2X 13 7 k := by decide +kernel

theorem transform2X_c7_r14 : ∀ k,
    matrixX affine2 transform2Y 14 7 k = scaleTensor transformFactor2X transform2X 14 7 k := by decide +kernel

theorem transform2X_c7_r15 : ∀ k,
    matrixX affine2 transform2Y 15 7 k = scaleTensor transformFactor2X transform2X 15 7 k := by decide +kernel

theorem transform2X_c7_r16 : ∀ k,
    matrixX affine2 transform2Y 16 7 k = scaleTensor transformFactor2X transform2X 16 7 k := by decide +kernel

theorem transform2X_col7 : ∀ i k,
    matrixX affine2 transform2Y i 7 k = scaleTensor transformFactor2X transform2X i 7 k := by
  intro i k
  fin_cases i
  · exact transform2X_c7_r0 k
  · exact transform2X_c7_r1 k
  · exact transform2X_c7_r2 k
  · exact transform2X_c7_r3 k
  · exact transform2X_c7_r4 k
  · exact transform2X_c7_r5 k
  · exact transform2X_c7_r6 k
  · exact transform2X_c7_r7 k
  · exact transform2X_c7_r8 k
  · exact transform2X_c7_r9 k
  · exact transform2X_c7_r10 k
  · exact transform2X_c7_r11 k
  · exact transform2X_c7_r12 k
  · exact transform2X_c7_r13 k
  · exact transform2X_c7_r14 k
  · exact transform2X_c7_r15 k
  · exact transform2X_c7_r16 k

theorem transform2X_c8_r0 : ∀ k,
    matrixX affine2 transform2Y 0 8 k = scaleTensor transformFactor2X transform2X 0 8 k := by decide +kernel

theorem transform2X_c8_r1 : ∀ k,
    matrixX affine2 transform2Y 1 8 k = scaleTensor transformFactor2X transform2X 1 8 k := by decide +kernel

theorem transform2X_c8_r2 : ∀ k,
    matrixX affine2 transform2Y 2 8 k = scaleTensor transformFactor2X transform2X 2 8 k := by decide +kernel

theorem transform2X_c8_r3 : ∀ k,
    matrixX affine2 transform2Y 3 8 k = scaleTensor transformFactor2X transform2X 3 8 k := by decide +kernel

theorem transform2X_c8_r4 : ∀ k,
    matrixX affine2 transform2Y 4 8 k = scaleTensor transformFactor2X transform2X 4 8 k := by decide +kernel

theorem transform2X_c8_r5 : ∀ k,
    matrixX affine2 transform2Y 5 8 k = scaleTensor transformFactor2X transform2X 5 8 k := by decide +kernel

theorem transform2X_c8_r6 : ∀ k,
    matrixX affine2 transform2Y 6 8 k = scaleTensor transformFactor2X transform2X 6 8 k := by decide +kernel

theorem transform2X_c8_r7 : ∀ k,
    matrixX affine2 transform2Y 7 8 k = scaleTensor transformFactor2X transform2X 7 8 k := by decide +kernel

theorem transform2X_c8_r8 : ∀ k,
    matrixX affine2 transform2Y 8 8 k = scaleTensor transformFactor2X transform2X 8 8 k := by decide +kernel

theorem transform2X_c8_r9 : ∀ k,
    matrixX affine2 transform2Y 9 8 k = scaleTensor transformFactor2X transform2X 9 8 k := by decide +kernel

theorem transform2X_c8_r10 : ∀ k,
    matrixX affine2 transform2Y 10 8 k = scaleTensor transformFactor2X transform2X 10 8 k := by decide +kernel

theorem transform2X_c8_r11 : ∀ k,
    matrixX affine2 transform2Y 11 8 k = scaleTensor transformFactor2X transform2X 11 8 k := by decide +kernel

theorem transform2X_c8_r12 : ∀ k,
    matrixX affine2 transform2Y 12 8 k = scaleTensor transformFactor2X transform2X 12 8 k := by decide +kernel

theorem transform2X_c8_r13 : ∀ k,
    matrixX affine2 transform2Y 13 8 k = scaleTensor transformFactor2X transform2X 13 8 k := by decide +kernel

theorem transform2X_c8_r14 : ∀ k,
    matrixX affine2 transform2Y 14 8 k = scaleTensor transformFactor2X transform2X 14 8 k := by decide +kernel

theorem transform2X_c8_r15 : ∀ k,
    matrixX affine2 transform2Y 15 8 k = scaleTensor transformFactor2X transform2X 15 8 k := by decide +kernel

theorem transform2X_c8_r16 : ∀ k,
    matrixX affine2 transform2Y 16 8 k = scaleTensor transformFactor2X transform2X 16 8 k := by decide +kernel

theorem transform2X_col8 : ∀ i k,
    matrixX affine2 transform2Y i 8 k = scaleTensor transformFactor2X transform2X i 8 k := by
  intro i k
  fin_cases i
  · exact transform2X_c8_r0 k
  · exact transform2X_c8_r1 k
  · exact transform2X_c8_r2 k
  · exact transform2X_c8_r3 k
  · exact transform2X_c8_r4 k
  · exact transform2X_c8_r5 k
  · exact transform2X_c8_r6 k
  · exact transform2X_c8_r7 k
  · exact transform2X_c8_r8 k
  · exact transform2X_c8_r9 k
  · exact transform2X_c8_r10 k
  · exact transform2X_c8_r11 k
  · exact transform2X_c8_r12 k
  · exact transform2X_c8_r13 k
  · exact transform2X_c8_r14 k
  · exact transform2X_c8_r15 k
  · exact transform2X_c8_r16 k

theorem transform2X_c9_r0 : ∀ k,
    matrixX affine2 transform2Y 0 9 k = scaleTensor transformFactor2X transform2X 0 9 k := by decide +kernel

theorem transform2X_c9_r1 : ∀ k,
    matrixX affine2 transform2Y 1 9 k = scaleTensor transformFactor2X transform2X 1 9 k := by decide +kernel

theorem transform2X_c9_r2 : ∀ k,
    matrixX affine2 transform2Y 2 9 k = scaleTensor transformFactor2X transform2X 2 9 k := by decide +kernel

theorem transform2X_c9_r3 : ∀ k,
    matrixX affine2 transform2Y 3 9 k = scaleTensor transformFactor2X transform2X 3 9 k := by decide +kernel

theorem transform2X_c9_r4 : ∀ k,
    matrixX affine2 transform2Y 4 9 k = scaleTensor transformFactor2X transform2X 4 9 k := by decide +kernel

theorem transform2X_c9_r5 : ∀ k,
    matrixX affine2 transform2Y 5 9 k = scaleTensor transformFactor2X transform2X 5 9 k := by decide +kernel

theorem transform2X_c9_r6 : ∀ k,
    matrixX affine2 transform2Y 6 9 k = scaleTensor transformFactor2X transform2X 6 9 k := by decide +kernel

theorem transform2X_c9_r7 : ∀ k,
    matrixX affine2 transform2Y 7 9 k = scaleTensor transformFactor2X transform2X 7 9 k := by decide +kernel

theorem transform2X_c9_r8 : ∀ k,
    matrixX affine2 transform2Y 8 9 k = scaleTensor transformFactor2X transform2X 8 9 k := by decide +kernel

theorem transform2X_c9_r9 : ∀ k,
    matrixX affine2 transform2Y 9 9 k = scaleTensor transformFactor2X transform2X 9 9 k := by decide +kernel

theorem transform2X_c9_r10 : ∀ k,
    matrixX affine2 transform2Y 10 9 k = scaleTensor transformFactor2X transform2X 10 9 k := by decide +kernel

theorem transform2X_c9_r11 : ∀ k,
    matrixX affine2 transform2Y 11 9 k = scaleTensor transformFactor2X transform2X 11 9 k := by decide +kernel

theorem transform2X_c9_r12 : ∀ k,
    matrixX affine2 transform2Y 12 9 k = scaleTensor transformFactor2X transform2X 12 9 k := by decide +kernel

theorem transform2X_c9_r13 : ∀ k,
    matrixX affine2 transform2Y 13 9 k = scaleTensor transformFactor2X transform2X 13 9 k := by decide +kernel

theorem transform2X_c9_r14 : ∀ k,
    matrixX affine2 transform2Y 14 9 k = scaleTensor transformFactor2X transform2X 14 9 k := by decide +kernel

theorem transform2X_c9_r15 : ∀ k,
    matrixX affine2 transform2Y 15 9 k = scaleTensor transformFactor2X transform2X 15 9 k := by decide +kernel

theorem transform2X_c9_r16 : ∀ k,
    matrixX affine2 transform2Y 16 9 k = scaleTensor transformFactor2X transform2X 16 9 k := by decide +kernel

theorem transform2X_col9 : ∀ i k,
    matrixX affine2 transform2Y i 9 k = scaleTensor transformFactor2X transform2X i 9 k := by
  intro i k
  fin_cases i
  · exact transform2X_c9_r0 k
  · exact transform2X_c9_r1 k
  · exact transform2X_c9_r2 k
  · exact transform2X_c9_r3 k
  · exact transform2X_c9_r4 k
  · exact transform2X_c9_r5 k
  · exact transform2X_c9_r6 k
  · exact transform2X_c9_r7 k
  · exact transform2X_c9_r8 k
  · exact transform2X_c9_r9 k
  · exact transform2X_c9_r10 k
  · exact transform2X_c9_r11 k
  · exact transform2X_c9_r12 k
  · exact transform2X_c9_r13 k
  · exact transform2X_c9_r14 k
  · exact transform2X_c9_r15 k
  · exact transform2X_c9_r16 k

theorem transform2X_c10_r0 : ∀ k,
    matrixX affine2 transform2Y 0 10 k = scaleTensor transformFactor2X transform2X 0 10 k := by decide +kernel

theorem transform2X_c10_r1 : ∀ k,
    matrixX affine2 transform2Y 1 10 k = scaleTensor transformFactor2X transform2X 1 10 k := by decide +kernel

theorem transform2X_c10_r2 : ∀ k,
    matrixX affine2 transform2Y 2 10 k = scaleTensor transformFactor2X transform2X 2 10 k := by decide +kernel

theorem transform2X_c10_r3 : ∀ k,
    matrixX affine2 transform2Y 3 10 k = scaleTensor transformFactor2X transform2X 3 10 k := by decide +kernel

theorem transform2X_c10_r4 : ∀ k,
    matrixX affine2 transform2Y 4 10 k = scaleTensor transformFactor2X transform2X 4 10 k := by decide +kernel

theorem transform2X_c10_r5 : ∀ k,
    matrixX affine2 transform2Y 5 10 k = scaleTensor transformFactor2X transform2X 5 10 k := by decide +kernel

theorem transform2X_c10_r6 : ∀ k,
    matrixX affine2 transform2Y 6 10 k = scaleTensor transformFactor2X transform2X 6 10 k := by decide +kernel

theorem transform2X_c10_r7 : ∀ k,
    matrixX affine2 transform2Y 7 10 k = scaleTensor transformFactor2X transform2X 7 10 k := by decide +kernel

theorem transform2X_c10_r8 : ∀ k,
    matrixX affine2 transform2Y 8 10 k = scaleTensor transformFactor2X transform2X 8 10 k := by decide +kernel

theorem transform2X_c10_r9 : ∀ k,
    matrixX affine2 transform2Y 9 10 k = scaleTensor transformFactor2X transform2X 9 10 k := by decide +kernel

theorem transform2X_c10_r10 : ∀ k,
    matrixX affine2 transform2Y 10 10 k = scaleTensor transformFactor2X transform2X 10 10 k := by decide +kernel

theorem transform2X_c10_r11 : ∀ k,
    matrixX affine2 transform2Y 11 10 k = scaleTensor transformFactor2X transform2X 11 10 k := by decide +kernel

theorem transform2X_c10_r12 : ∀ k,
    matrixX affine2 transform2Y 12 10 k = scaleTensor transformFactor2X transform2X 12 10 k := by decide +kernel

theorem transform2X_c10_r13 : ∀ k,
    matrixX affine2 transform2Y 13 10 k = scaleTensor transformFactor2X transform2X 13 10 k := by decide +kernel

theorem transform2X_c10_r14 : ∀ k,
    matrixX affine2 transform2Y 14 10 k = scaleTensor transformFactor2X transform2X 14 10 k := by decide +kernel

theorem transform2X_c10_r15 : ∀ k,
    matrixX affine2 transform2Y 15 10 k = scaleTensor transformFactor2X transform2X 15 10 k := by decide +kernel

theorem transform2X_c10_r16 : ∀ k,
    matrixX affine2 transform2Y 16 10 k = scaleTensor transformFactor2X transform2X 16 10 k := by decide +kernel

theorem transform2X_col10 : ∀ i k,
    matrixX affine2 transform2Y i 10 k = scaleTensor transformFactor2X transform2X i 10 k := by
  intro i k
  fin_cases i
  · exact transform2X_c10_r0 k
  · exact transform2X_c10_r1 k
  · exact transform2X_c10_r2 k
  · exact transform2X_c10_r3 k
  · exact transform2X_c10_r4 k
  · exact transform2X_c10_r5 k
  · exact transform2X_c10_r6 k
  · exact transform2X_c10_r7 k
  · exact transform2X_c10_r8 k
  · exact transform2X_c10_r9 k
  · exact transform2X_c10_r10 k
  · exact transform2X_c10_r11 k
  · exact transform2X_c10_r12 k
  · exact transform2X_c10_r13 k
  · exact transform2X_c10_r14 k
  · exact transform2X_c10_r15 k
  · exact transform2X_c10_r16 k

theorem transform2X_c11_r0 : ∀ k,
    matrixX affine2 transform2Y 0 11 k = scaleTensor transformFactor2X transform2X 0 11 k := by decide +kernel

theorem transform2X_c11_r1 : ∀ k,
    matrixX affine2 transform2Y 1 11 k = scaleTensor transformFactor2X transform2X 1 11 k := by decide +kernel

theorem transform2X_c11_r2 : ∀ k,
    matrixX affine2 transform2Y 2 11 k = scaleTensor transformFactor2X transform2X 2 11 k := by decide +kernel

theorem transform2X_c11_r3 : ∀ k,
    matrixX affine2 transform2Y 3 11 k = scaleTensor transformFactor2X transform2X 3 11 k := by decide +kernel

theorem transform2X_c11_r4 : ∀ k,
    matrixX affine2 transform2Y 4 11 k = scaleTensor transformFactor2X transform2X 4 11 k := by decide +kernel

theorem transform2X_c11_r5 : ∀ k,
    matrixX affine2 transform2Y 5 11 k = scaleTensor transformFactor2X transform2X 5 11 k := by decide +kernel

theorem transform2X_c11_r6 : ∀ k,
    matrixX affine2 transform2Y 6 11 k = scaleTensor transformFactor2X transform2X 6 11 k := by decide +kernel

theorem transform2X_c11_r7 : ∀ k,
    matrixX affine2 transform2Y 7 11 k = scaleTensor transformFactor2X transform2X 7 11 k := by decide +kernel

theorem transform2X_c11_r8 : ∀ k,
    matrixX affine2 transform2Y 8 11 k = scaleTensor transformFactor2X transform2X 8 11 k := by decide +kernel

theorem transform2X_c11_r9 : ∀ k,
    matrixX affine2 transform2Y 9 11 k = scaleTensor transformFactor2X transform2X 9 11 k := by decide +kernel

theorem transform2X_c11_r10 : ∀ k,
    matrixX affine2 transform2Y 10 11 k = scaleTensor transformFactor2X transform2X 10 11 k := by decide +kernel

theorem transform2X_c11_r11 : ∀ k,
    matrixX affine2 transform2Y 11 11 k = scaleTensor transformFactor2X transform2X 11 11 k := by decide +kernel

theorem transform2X_c11_r12 : ∀ k,
    matrixX affine2 transform2Y 12 11 k = scaleTensor transformFactor2X transform2X 12 11 k := by decide +kernel

theorem transform2X_c11_r13 : ∀ k,
    matrixX affine2 transform2Y 13 11 k = scaleTensor transformFactor2X transform2X 13 11 k := by decide +kernel

theorem transform2X_c11_r14 : ∀ k,
    matrixX affine2 transform2Y 14 11 k = scaleTensor transformFactor2X transform2X 14 11 k := by decide +kernel

theorem transform2X_c11_r15 : ∀ k,
    matrixX affine2 transform2Y 15 11 k = scaleTensor transformFactor2X transform2X 15 11 k := by decide +kernel

theorem transform2X_c11_r16 : ∀ k,
    matrixX affine2 transform2Y 16 11 k = scaleTensor transformFactor2X transform2X 16 11 k := by decide +kernel

theorem transform2X_col11 : ∀ i k,
    matrixX affine2 transform2Y i 11 k = scaleTensor transformFactor2X transform2X i 11 k := by
  intro i k
  fin_cases i
  · exact transform2X_c11_r0 k
  · exact transform2X_c11_r1 k
  · exact transform2X_c11_r2 k
  · exact transform2X_c11_r3 k
  · exact transform2X_c11_r4 k
  · exact transform2X_c11_r5 k
  · exact transform2X_c11_r6 k
  · exact transform2X_c11_r7 k
  · exact transform2X_c11_r8 k
  · exact transform2X_c11_r9 k
  · exact transform2X_c11_r10 k
  · exact transform2X_c11_r11 k
  · exact transform2X_c11_r12 k
  · exact transform2X_c11_r13 k
  · exact transform2X_c11_r14 k
  · exact transform2X_c11_r15 k
  · exact transform2X_c11_r16 k

#print axioms transform2X_col6

end D4Bound.SphericalSurplusSign.Bernstein16
