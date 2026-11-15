"""Generate integer Gram projection witnesses; Lean checks all identities against V7Data."""
from pathlib import Path
import json,math,argparse
from fractions import Fraction as Q
from census_gram_inputs import validate_inputs, integer
ROOT=Path(__file__).resolve().parents[1]; P=ROOT.parent
args_parser=argparse.ArgumentParser()
args_parser.add_argument('--check',action='store_true')
args=args_parser.parse_args()
def emit(path,text):
 if args.check:
  if path.read_text()!=text:raise SystemExit(f'Generated source mismatch: {path}')
 else:path.write_text(text)
read=lambda p:json.loads(p.read_text())
k=read(P/'data/v7/kernel.json');o=read(P/'data/v7/origin.json')
p=read(P/'verify/stage2_origin/source/target625/origin_completion/ACCEPTED_JOINT_COUNT_PROJECTION.json')
r=read(P/'verify/stage2_origin/reference/RADIAL_PLANES.json')
validate_inputs(k,o,p,r)
rays=k['blocks'][0]['rays'];V=[[integer(x) for x in row['vector'][1:]] for row in rays];weights=[integer(row['weight']) for row in rays]
B=[[Q(x) for x in row] for row in p['indicator_range_solutions']];G=[[Q(x) for x in row] for row in p['D_inverse']]
T=[[sum(B[i][l]*G[l][j] for l in range(5)) for j in range(5)] for i in range(49)]
duals=[[sum(Q(V[a][i])*T[i][j] for i in range(49)) for j in range(5)] for a in range(34)]
u=[Q(x) for x in o['u']];offsets=[sum(Q(a)*b for a,b in zip(v,u)) for v in V]
m=[Q(x) for x in p['count_offsets_m']]
def arr(v):return '#['+', '.join(map(str,v))+']'
def mat(v):return '#[\n'+',\n'.join(arr(row) for row in v)+'\n]'
def scaled(v):
 D=math.lcm(*(x.denominator for x in v));return D,[int(x*D) for x in v]
def scaledmat(v):
 D=math.lcm(*(x.denominator for row in v for x in row));return D,[[int(x*D) for x in row] for row in v]
s='''import D4Bound.V7Data
import Mathlib.Tactic

/-! Generated exact witnesses for the count projection; no result flags are imported. -/
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
s+=f'def rayWeights : Array ℤ := {arr(weights)}\n'
s+=f'def rayVectors : Array (Array ℤ) := {mat(V)}\n'
s+=f'def gramDen : ℤ := {integer(k["common_denominator"])}\n'
for name,v,isMat in [('dual',duals,True),('inverse',G,True),('origin',offsets,False),('countOffset',m,False)]:
 D,nums=scaledmat(v) if isMat else scaled(v)
 s+=f'def {name}Den : ℤ := {D}\n'
 s+=f'def {name}Nums : Array '+('(Array ℤ)' if isMat else 'ℤ')+' := '+(mat(nums) if isMat else arr(nums))+'\n'
s+='''
def ray (i : ℕ) : Ray := gramRays0.getD i ⟨0,[]⟩
def vectorDataOK : Bool := (List.range 34).all fun i =>
  decide ((rayWeights[i]! : ℚ) = (ray i).weight ∧
    (List.range 49).all (fun j => decide (((rayVectors[i]!)[j]! : ℚ) = (ray i).vector.getD j 0)) = true)
theorem gram_den_checked : (gramDen : ℚ) = gramDenominator := by decide +kernel
theorem den_pos : 0 < gramDen ∧ 0 < dualDen ∧ 0 < inverseDen ∧ 0 < originDen ∧ 0 < countOffsetDen := by decide +kernel

-- Range equations, multiplied through by the three positive denominators.
def rangeRowOK (k : ℕ) : Bool := (List.range 5).all fun j => decide (
  ((List.range 34).map fun i => rayWeights[i]!*(rayVectors[i]!)[k]!*(dualNums[i]!)[j]!).sum * inverseDen =
  gramDen*dualDen*((List.range 5).map fun l => if k/7 ≤ l then (inverseNums[l]!)[j]! else 0).sum)

def inverseRowOK (j : ℕ) : Bool := (List.range 5).all fun k => decide (
  ((List.range 34).map fun i => rayWeights[i]!*(dualNums[i]!)[j]!*(dualNums[i]!)[k]!).sum * inverseDen =
  gramDen*dualDen^2*(inverseNums[j]!)[k]!)
'''


s+='end D4Bound.V7.CensusGram\n'
emit(ROOT/'D4Bound/V7CensusGramData.lean',s)
print(('PASS: checked' if args.check else 'Wrote')+' integer projection data and 54 kernel checks:',len(s),'characters')
# A separate small table for the twelve affine witnesses and their actual ray-centres.
planes='''import D4Bound.V7Data
import Mathlib.Tactic
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
def rat(q):
 q=Q(q);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator} : ℚ)'
def qlist(v):return '['+', '.join(rat(x) for x in v)+']'
for a,row in enumerate(r):
 planes+=f'def planeCentres{a} : List ℚ := {qlist(row["ray_centers"])}\n'
 planes+=f'def planeLinear{a} : List ℚ := {qlist(row["physical_radial_linear_coefficients"])}\n'
 planes+=f'def planeConstant{a} : ℚ := {rat(row["constant"])}\n'
 planes+=f'def planeLowers{a} : List ℚ := {qlist(row["near_shell_lower_bounds"])}\n'
 planes+=f'def planeCounts{a} : List ℚ := {qlist(row["affine_count_coefficients"])}\n'
planes+='end D4Bound.V7.CensusGram\n'
emit(ROOT/'D4Bound/V7CensusGramPlaneData.lean',planes)
print(('PASS: checked' if args.check else 'Wrote')+' affine plane witness data:',len(planes),'characters')

for chunk in range(8):
 out="import D4Bound.V7CensusGramData\nnamespace D4Bound.V7.CensusGram\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
 if chunk<7:
  for row in range(7*chunk,7*chunk+7):out+=f"theorem range_row_{row} : rangeRowOK {row} = true := by decide +kernel\n"
 else:
  out+="theorem vector_data_checked : vectorDataOK = true := by decide +kernel\n"
  for row in range(5):out+=f"theorem inverse_row_{row} : inverseRowOK {row} = true := by decide +kernel\n"
 out+="end D4Bound.V7.CensusGram\n"
 emit(ROOT/f'D4Bound/V7CensusGramCheck{chunk}.lean',out)
