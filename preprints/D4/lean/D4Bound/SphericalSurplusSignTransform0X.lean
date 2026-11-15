import D4Bound.SphericalSurplusSignTransform0XCol0

import D4Bound.SphericalSurplusSignTransform0XCol1

import D4Bound.SphericalSurplusSignTransform0XCol2

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign.Bernstein16

theorem transform0X_eq : matrixX affine0 transform0Y = scaleTensor transformFactor0X transform0X := by
  funext i j k
  fin_cases j
  · exact transform0X_col0 i k
  · exact transform0X_col1 i k
  · exact transform0X_col2 i k
  · exact transform0X_col3 i k
  · exact transform0X_col4 i k
  · exact transform0X_col5 i k
  · exact transform0X_col6 i k
  · exact transform0X_col7 i k
  · exact transform0X_col8 i k
  · exact transform0X_col9 i k
  · exact transform0X_col10 i k
  · exact transform0X_col11 i k
  · exact transform0X_col12 i k
  · exact transform0X_col13 i k
  · exact transform0X_col14 i k
  · exact transform0X_col15 i k
  · exact transform0X_col16 i k

#print axioms transform0X_eq

end D4Bound.SphericalSurplusSign.Bernstein16
