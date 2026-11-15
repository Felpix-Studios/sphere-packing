import D4Bound.SphericalSurplusSignTransformBound16

set_option maxHeartbeats 0
set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

lemma matrixX_scale (T : I → I → ℤ) (d : ℤ) (p : Tensor) :
    matrixX T (scaleTensor d p) = scaleTensor d (matrixX T p) := by
  funext i j k
  simp only [matrixX, scaleTensor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma matrixY_scale (T : I → I → ℤ) (d : ℤ) (p : Tensor) :
    matrixY T (scaleTensor d p) = scaleTensor d (matrixY T p) := by
  funext i j k
  simp only [matrixY, scaleTensor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Removing a common integer factor after each exact matrix multiplication
keeps proof data small; the factor is restored by this checked identity. -/
lemma matrixXYZ_scaled (T : I → I → ℤ) (p z y x : Tensor) (gz gy gx : ℤ)
    (hz : matrixZ T p = scaleTensor gz z)
    (hy : matrixY T z = scaleTensor gy y)
    (hx : matrixX T y = scaleTensor gx x) :
    matrixX T (matrixY T (matrixZ T p)) = scaleTensor (gz * gy * gx) x := by
  rw [hz, matrixY_scale, hy, matrixX_scale, matrixX_scale, hx]
  funext i j k
  simp only [scaleTensor]
  ring

#print axioms matrixXYZ_scaled
end D4Bound.SphericalSurplusSign.Bernstein16
