"""Generate untrusted exact data for the degree-16 moderate graph polynomial.

The generated Lean module checks signs, coverage and the harmonic identity.
"""
import argparse
import json
import math
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "verify/stage1_v7/record/current/six_exterior_graph_route/moderate_exterior_graph_certificate.json"
TARGET = ROOT / "lean/D4Bound/ModerateGraphCert.lean"


def rat(q):
    return f"({q.numerator}/{q.denominator})"


def generate():
    data = json.loads(SOURCE.read_text())
    assert data["ambient_dimension"] == 4 and data["harmonic_degree"] == 16
    assert data["spherical_cutoff"] == "7/9"
    assert data["target_angular_interval"] == ["-4/5", "-11/20"]
    a = list(map(Q, data["harmonic_coefficients"]))
    p = list(map(Q, data["power_coefficients"]))
    assert len(a) == len(p) == 17 and a[0] > 0 and all(c >= 0 for c in a)
    lines = ["import D4Bound.AnnularCert", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0", "set_option Elab.async false",
             "open Finset", "namespace D4Bound.ModerateGraphCertificate",
             "noncomputable section", "open AnnularCertificate",
             "def coefficients : Fin 16 → ℝ := ![" + ", ".join(rat(a[k]/(k+1)) for k in range(1,17)) + "]",
             "def rest (t : ℝ) : ℝ := ∑ i : Fin 16, coefficients i * (Polynomial.Chebyshev.U ℝ ((i.val+1 : ℕ) : ℤ)).eval t",
             "theorem rest_energy : SphereEnergyNonneg rest := by\n  apply sphereEnergy_sum\n  intro i _\n  fin_cases i <;> norm_num [coefficients]",
             f"theorem diagonal : {rat(a[0])} + rest 1 = {rat(sum(a))} := by\n  norm_num [rest, coefficients, Fin.sum_univ_succ, Polynomial.Chebyshev.U_eval_one]"]
    for name, lo, hi, offset in [("whole",Q(-1),Q(7,9),Q(0)),("band",Q(-4,5),Q(-11,20),Q(1))]:
        r = [-sum((c*math.comb(j,k)*lo**(j-k)*(hi-lo)**k for j,c in enumerate(p) if j>=k),Q()) for k in range(17)]
        r[0] -= offset
        den = math.lcm(*(c.denominator for c in r))
        nums = [int(c*den) for c in r]
        leaves, stack = [], [(0,0)]
        nodes = 0
        while stack:
            A,k = stack.pop()
            nodes += 1
            assert k < 50 and nodes < 20000, "exact interval cover did not close within diagnostic gate"
            d = 2**k
            cs = [sum(nums[j]*math.comb(j,i)*A**(j-i)*d**(16-j) for j in range(i,17)) for i in range(17)]
            lb = 0
            for c in reversed(cs):
                lb = c + min(lb,0)
            if lb>0:
                leaves.append((A,k,1))
            else:
                stack.extend([(2*A+1,k+1),(2*A,k+1)])
        print(name, "nodes", nodes, "leaves",len(leaves), flush=True)
        lines += [f"def {name}Numerators : List ℤ := {nums}", f"def {name}Denominator : ℤ := {den}",
                  f"def {name}Leaves : List (ℕ × ℕ × ℕ) := {leaves}",
                  f"theorem {name}_checked : chainOK {name}Numerators 0 0 {name}Leaves 1 0 = true := by decide +kernel",
                  f"theorem {name}_endpoint : 0 < evalZ {name}Numerators 1 := by norm_num [{name}Numerators, evalZ]",
                  f"theorem {name}_identity (u : ℝ) :\n    {rat(a[0])} + rest ({rat(lo)}+{rat(hi-lo)}*u) + {rat(offset)} =\n      -evalZ {name}Numerators u / {name}Denominator := by\n  norm_num [rest, coefficients, Fin.sum_univ_succ, {', '.join('U'+str(k) for k in range(1,17))}, {name}Numerators, {name}Denominator, evalZ]\n  <;> ring",
                  f"""theorem {name}_sign (t : ℝ) (ht0 : {rat(lo)} ≤ t) (ht1 : t ≤ {rat(hi)}) :
    {rat(a[0])} + rest t + {rat(offset)} ≤ 0 := by
  let u : ℝ := (t-{rat(lo)})/{rat(hi-lo)}
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ {name}Numerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound {name}Numerators {name}Leaves 0 0 1 0 {name}_checked u
        (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using {name}_endpoint
  have he := {name}_identity u
  have hu : {rat(lo)}+{rat(hi-lo)}*u=t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [{name}Denominator])"""]
    lines += ["end", "end D4Bound.ModerateGraphCertificate", ""]
    return "\n\n".join(lines)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text = generate()
    assert len(text.encode()) < 1024**2
    if args.check:
        assert TARGET.read_text() == text
    else:
        TARGET.write_text(text)
    print("PASS generation only; Lean replay required", len(text), "bytes")
