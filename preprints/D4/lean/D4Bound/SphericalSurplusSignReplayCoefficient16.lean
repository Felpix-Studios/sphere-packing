import D4Bound.SphericalSurplusSignTree16
namespace D4Bound.SphericalSurplusSign.Bernstein16.ArrayData
def coefficient (right : Bool) (i h : ℕ) : ℤ :=
  if right then
    if i ≤ h then (Nat.choose (16-i) (h-i) : ℤ)*2^i else 0
  else if h ≤ i then (Nat.choose i h : ℤ)*2^(16-i) else 0
end D4Bound.SphericalSurplusSign.Bernstein16.ArrayData
