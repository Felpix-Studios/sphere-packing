"""Generate/check uniform exact-origin and affine-plane Lean proof modules.

The output contains actual kernel-checked equations, not imported result flags.
The static generic origin and supporting-plane soundness proofs are separate.
"""
from pathlib import Path
import argparse
P=Path(__file__).resolve().parents[1]/'D4Bound'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
outputs={}
for part in range(7):
 s='import D4Bound.V7CensusGramOrigin\nnamespace D4Bound.V7.CensusGram\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
 for k in range(7*part,7*part+7):s+=f'theorem origin_row_{k} : originRowOK {k} = true := by decide +kernel\n'
 outputs[f'V7CensusGramOriginCheck{part}.lean']=s+'end D4Bound.V7.CensusGram\n'
for j in range(12):
 s=f'''import D4Bound.V7CensusGramPlanesBasic
import D4Bound.V7CensusGramPlane{j}
import D4Bound.CensusArithmetic
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
 s+=f'theorem plane{j}_constant : planeConstantOK planeCentres{j} planeConstant{j} = true := by decide +kernel\n'
 for k in range(49):s+=f'theorem plane{j}_row{k} : planeRowOK planeCentres{j} planeLinear{j} {k} = true := by decide +kernel\n'
 s+=f'''theorem plane{j}_rows (k : ℕ) (hk : k < 49) :
    planeRowOK planeCentres{j} planeLinear{j} k = true := by
  interval_cases k
'''+''.join(f'  · exact plane{j}_row{k}\n' for k in range(49))
 s+='noncomputable section\n'
 s+=f'''theorem plane{j}_census_identity (X : Finset E4) :
    (planeConstant{j} : ℝ) + ((List.range 5).map fun i => (planeCounts{j}.getD i 0 : ℝ)*
      (countWithin X ((breaks.getD (i+1) 0 : ℚ) : ℝ) : ℝ)).sum =
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[{j}]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) := by
  norm_num [planeConstant{j}, planeCounts{j}, List.range_succ, breaks,
    CensusArithmetic.affine, CensusArithmetic.planeCoeffs, CensusArithmetic.denominator,
    CensusArithmetic.ofNeighbourhood, nearCount, R1, R2, R3, R4, R5]
  ring

theorem gram_energy_ge_plane{j} (X : Finset E4) (hX : (0 : E4) ∉ X)
    (hR : ∀ x ∈ X, ‖x‖ ≤ 7/4) (h1 : ∀ x ∈ X, 1 ≤ ‖x‖) :
    (CensusArithmetic.affine (CensusArithmetic.planeCoeffs[{j}]!)
      (CensusArithmetic.ofNeighbourhood X) : ℝ) / (CensusArithmetic.denominator : ℝ) ≤
    gramEnergy X := by
  rw [← plane{j}_census_identity]
  exact gram_plane_floor planeCentres{j} planeLinear{j} planeCounts{j} planeConstant{j}
    plane{j}_constant plane{j}_rows X hX hR (fun x hx => plane{j}_radial ‖x‖ (h1 x hx) (hR x hx))
end
end D4Bound.V7.CensusGram
'''
 if j>=3:
  s=s.replace('import D4Bound.CensusArithmetic','import D4Bound.CensusArithmetic\nimport D4Bound.V7CensusGramCensusIdentity')
  start=s.index(f'  norm_num [planeConstant{j}, planeCounts{j}, List.range_succ, breaks,')
  end=s.index('\n\ntheorem gram_energy_ge_plane',start)
  s=s[:start]+f'''  apply affine_count_identity planeCounts{j} planeConstant{j}
    (CensusArithmetic.planeCoeffs[{j}]!)
  · decide +kernel
  · intro i hi
    interval_cases i <;> decide +kernel'''+s[end:]
 outputs[f'V7CensusGramPlaneCheck{j}.lean']=s
for name,s in outputs.items():
 path=P/name
 if args.check:
  if path.read_text()!=s:raise SystemExit(f'Generated source mismatch: {path}')
 else:path.write_text(s)
print(('PASS: checked' if args.check else 'Generated')+f' {len(outputs)} exact Gram witness modules')
