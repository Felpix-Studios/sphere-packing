import D4Bound.SphericalSurplusSignTransform2XCol0

import D4Bound.SphericalSurplusSignTransform2XCol1

import D4Bound.SphericalSurplusSignTransform2XCol2

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem transform2X_eq : matrixX affine2 transform2Y = scaleTensor transformFactor2X transform2X := by
  funext i j k
  fin_cases j
  · exact transform2X_col0 i k
  · exact transform2X_col1 i k
  · exact transform2X_col2 i k
  · exact transform2X_col3 i k
  · exact transform2X_col4 i k
  · exact transform2X_col5 i k
  · exact transform2X_col6 i k
  · exact transform2X_col7 i k
  · exact transform2X_col8 i k
  · exact transform2X_col9 i k
  · exact transform2X_col10 i k
  · exact transform2X_col11 i k
  · exact transform2X_col12 i k
  · exact transform2X_col13 i k
  · exact transform2X_col14 i k
  · exact transform2X_col15 i k
  · exact transform2X_col16 i k

#print axioms transform2X_eq

end D4Bound.SphericalSurplusSign.Bernstein16
