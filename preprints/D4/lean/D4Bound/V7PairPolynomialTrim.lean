import D4Bound.V7PairPolynomialDef

/-! Removing trailing zero coefficients is an exact polynomial operation. -/
namespace D4Bound.V7.PairPoly

def trim : Poly → Poly
  | [] => []
  | a::p => let t := trim p
    if a = 0 ∧ t = [] then [] else a::t

end D4Bound.V7.PairPoly
