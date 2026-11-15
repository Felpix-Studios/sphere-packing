"""Generate the 84 full native cyclic case modules and their assembly.

Writes into ../D4Bound:
  V7CyclicNativeParams.lean       shared parameters (cap filter, unit, fuel)
  V7CyclicNativeUnits.lean        per-case Bernstein unit 2^-e: for p <= 2, k >= 5,
                                  e = 38 - ceil(18 log2(2 R_p+1 R_q+1 R_k+1)), so root coefficients stay
                                  below 2^31 (Lean small Int); e = 40 otherwise
  V7CyclicNativeF{p}{q}{k}.lean   one native_decide of `fullCheckG` per full case, p <= q <= k
  V7CyclicNativeSign.lean         CyclicSign V7.kernel from the 84 checks and the exterior cases
The 28 exterior cases are proved elsewhere (outside agent).
Usage: python3 gen_cyclic_native_cases.py [--fuel N]
"""
import argparse
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
# cases whose unit is set by an override (see oexp); EXPLICIT_EXP: exponent e of 2^-e
# for cases where the oexp unit was too coarse (F556 FAILed at 2^10, run cf-case-F556-v3)
EXPLICIT_EXP = {(5, 5, 6): 0}
OVERRIDE_CASES = [(0, 5, 6), (3, 4, 6), (3, 5, 6), (4, 4, 6), (4, 5, 5), (4, 5, 6), (4, 6, 6), (5, 5, 5), (5, 5, 6), (5, 6, 6), (6, 6, 6)]
OUT = HERE.parent / 'D4Bound'

def unit_lit(e):
    return f'1/2^{e}' if e >= 0 else f'2^{-e}'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fuel', type=int, default=64)
    args = ap.parse_args()
    full = [(p, q, k) for p in range(7) for q in range(p, 7) for k in range(q, 7)]
    ext = [(p, q) for p in range(7) for q in range(p, 7)]
    assert len(full) == 84 and len(ext) == 28
    (OUT / 'V7CyclicNativeParams.lean').write_text(f'''import D4Bound.V7CyclicNativeFullG

/-! Shared parameters of the native cyclic case checks. Any choice is sound. -/
namespace D4Bound.V7
open CyclicNative

/-- Caps with weight times largest radial coefficient below 1e-11 get lower bound 0. -/
def capUse (c : Cap) : Bool := decide ((1:ℚ)/10^11 ≤ c.weight * c.vector.foldl max 0)

def caseUnit : ℚ := 1/2^40
def caseFuel : ℕ := {args.fuel}

end D4Bound.V7
''')
    br = [1, 501473/500000, 1005643/1000000, 50379/50000, 50767/50000, 102597/100000, 1.5, 1.75]
    def uexp(p, q, k):
        # coarse unit only for the slow class p <= 2, k >= 5; 2^-40 elsewhere
        if p <= 2 and k >= 5:
            return 38 - math.ceil(18 * math.log2(2 * br[p+1] * br[q+1] * br[k+1]))
        return 40
    arms = '\n'.join(f'  | {p}, {q}, {k} => {unit_lit(uexp(p, q, k))}' for p, q, k in full)
    # Per-case overrides, written as a literal in the case module and in `unitFinal` (Sign), so
    # that V7CyclicNativeUnits (imported by every case module) stays unchanged.
    # e = 44 - ceil(18 log2(2 R_(p+1) R_(q+1) R_(k+1))): root coefficients about 31 bits.
    def oexp(p, q, k):
        return 44 - math.ceil(18 * math.log2(2 * br[p+1] * br[q+1] * br[k+1]))
    OVERRIDE = {c: oexp(*c) for c in OVERRIDE_CASES}
    OVERRIDE.update(EXPLICIT_EXP)
    def unit_expr(p, q, k):
        return f'({unit_lit(OVERRIDE[(p, q, k)])})' if (p, q, k) in OVERRIDE else f'(caseUnitG {p} {q} {k})'
    oarms = ''.join(f'  | {p}, {q}, {k} => {unit_lit(e)}\n' for (p, q, k), e in sorted(OVERRIDE.items()))
    (OUT / 'V7CyclicNativeUnits.lean').write_text(f'''import D4Bound.V7CyclicNativeParams

/-! Per-case Bernstein units of the full cyclic checks (any positive choice is sound).
For `p ≤ 2, k ≥ 5`, `2^-e` with `e = 38 - ceil(18 log2(2 R_(p+1) R_(q+1) R_(k+1)))` keeps the
root coefficients below `2^31`, so the subdivision runs on Lean small integers; `2^-40`
elsewhere. -/
namespace D4Bound.V7

def caseUnitG : ℕ → ℕ → ℕ → ℚ
{arms}
  | _, _, _ => 1/2^40

end D4Bound.V7
''')
    for p, q, k in full:
        (OUT / f'V7CyclicNativeF{p}{q}{k}.lean').write_text(f'''import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case ({p},{q},{k}). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck{p}{q}{k} : fullCheckG capUse {unit_expr(p, q, k)} caseFuel {p} {q} {k} = true := by
  native_decide

end D4Bound.V7
''')
    imports = '\n'.join(f'import D4Bound.V7CyclicNativeF{p}{q}{k}' for p, q, k in full)
    fh = '\n'.join(f'  have h{p}{q}{k} : fullCheckG capUse (unitFinal {p} {q} {k}) caseFuel {p} {q} {k} = true :=\n    fullCheck{p}{q}{k}' for p, q, k in full)
    (OUT / 'V7CyclicNativeSign.lean').write_text(f'''{imports}

/-! `CyclicSign V7.kernel` from the 84 full native checks and the exterior cases. -/
namespace D4Bound.V7
open CyclicNative

/-- The unit of each case module: `caseUnitG` except the per-case overrides. -/
def unitFinal : ℕ → ℕ → ℕ → ℚ
{oarms}  | p, q, k => caseUnitG p q k

theorem native_full_checks : ∀ p ∈ fullCases,
    fullCheckG capUse (unitFinal p.1 p.2.1 p.2.2) caseFuel p.1 p.2.1 p.2.2 = true := by
{fh}
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ hp
  simp only [fullCases, Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk] at hp
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | assumption

/-- The cyclic sign of the concrete V7 kernel, given the 28 exterior cases. -/
theorem v7_cyclic_sign_of_outside (outside : ∀ p ∈ outsideCases, ∀ r s d : ℝ,
      RegionOwns p.1.val r → RegionOwns p.2.val s →
      r ≤ s → 7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) : CyclicSign kernel := by
  apply cyclicSign_of_112_cases _ outside
  intro p hp r s d hr hs hd _ _
  exact full_case_of_G p.1 p.2.1 p.2.2 p.1.isLt p.2.1.isLt p.2.2.isLt capUse _ caseFuel
    (native_full_checks p hp) hr hs hd

end D4Bound.V7

#print axioms D4Bound.V7.v7_cyclic_sign_of_outside
''')
    print('wrote', len(full), 'full modules')

if __name__ == '__main__':
    main()
