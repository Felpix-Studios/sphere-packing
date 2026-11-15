"""Export exact reduced Gram rays and physical fixed-count correction data."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import importlib.util
import json
import math
import sys

sys.dont_write_bytecode = True
PKG = Path(__file__).resolve().parents[2]
SOURCE = PKG/'verify/stage2_origin/source'
spec = importlib.util.spec_from_file_location('fixed_surplus_data',SOURCE/'target625/geometry/fixed_cardinality_spherical_algebra.py')
algebra = importlib.util.module_from_spec(spec)
spec.loader.exec_module(algebra)
ap = argparse.ArgumentParser()
ap.add_argument('--check',action='store_true')
args = ap.parse_args()
registry = json.loads((SOURCE/'target625/origin_completion/FINAL_ORIGIN_REGISTRY.json').read_text())
header = ['-- Generated exact reduced rays; semantic identities are checked separately.',
          'import D4Bound.SphericalSignPair', 'set_option maxHeartbeats 0',
          'set_option maxRecDepth 20000', 'set_option Elab.async false',
          'namespace D4Bound.SphericalSurplusSign', 'open SphericalSign']
for index, item in enumerate(registry['common_g_certificates']):
    d = json.loads((SOURCE/item['certificate']).read_text())
    cutoff = Q(d['s'])
    radial, rd = algebra.radial_basis(d['radial_degree'],cutoff,d['radial_basis'])
    fixed = d.get('fixed_count',0)
    rays = []
    for ell, block in enumerate(d['blocks']):
        for r in block:
            if not any(r):
                continue
            origin = r[0] if ell == 0 else 0
            v = ([0]+r[1:] if fixed else r[1:]) if ell == 0 else r
            c = [sum(int(radial[i,j])*v[i] for i in range(len(v))) for j in range(radial.shape[1])]
            while len(c)>1 and c[-1] == 0:
                c.pop()
            rays.append(f'⟨{ell},{origin},{c}⟩')
    free = d.get('fixed_origin_free',[0]*(d['radial_degree']+2))
    v0,b00,*h = free
    correction = [sum(int(radial[i+1,j])*h[i] for i in range(len(h))) for j in range(radial.shape[1])]
    while len(correction)>1 and correction[-1] == 0:
        correction.pop()
    scalar = [Q(0)]*len(d['scalar'])
    for ell,c in enumerate(d['scalar']):
        for j in range(ell//2+1):
            scalar[ell-2*j] += Q(c*(-1)**j*math.comb(ell-j,j)*2**(ell-2*j),d['scalar_scale']*(ell+1))
    scalar_den = math.lcm(*(c.denominator for c in scalar))
    scalar_power = [int(c*scalar_den) for c in scalar]
    repair = d.get('repair',d.get('bounded_cardinality_common_g_repair'))
    lines = header.copy()
    lines += [f'def rays{index} : List Ray := [\n  '+',\n  '.join(rays)+'\n]',
        f'def featureDen{index} : ℤ := {d["feature_scale"]*rd}',
        f'def originDen{index} : ℤ := {d["feature_scale"]}',
        f'def scalarPower{index} : List ℤ := {scalar_power}',
        f'def scalarPowerDen{index} : ℤ := {scalar_den}',
        f'def countM{index} : ℕ := {fixed-1 if fixed else 0}',
        f'def vNum{index} : ℤ := {v0}',
        f'def bNum{index} : ℤ := {b00}',
        f'def correction{index} : List ℤ := {correction}',
        f'def correctionDen{index} : ℤ := {d["feature_scale"]**2*rd}',
        f'def epsilon{index} : ℚ := {repair["scale"]}',
        f'def eta{index} : ℚ := {repair["pair_shift"]}',
        f'''noncomputable def g{index} (t : ℝ) : ℝ := evalZ scalarPower{index} t/scalarPowerDen{index}
noncomputable def F{index} (t : ℝ) : ℝ := evalZ correction{index} t/correctionDen{index}
noncomputable def v{index} : ℝ := (vNum{index}:ℝ)/(originDen{index}:ℝ)^2
noncomputable def b{index} : ℝ := (bNum{index}:ℝ)/(originDen{index}:ℝ)^2
noncomputable def kernel{index} (a b t : ℝ) : ℝ :=
  SphereCertificate.kernel Finset.univ (rayDegree rays{index}) (rayV rays{index} featureDen{index}) a b t + b{index} + F{index} a + F{index} b
noncomputable def coupling{index} (a : ℝ) : ℝ :=
  SphereCertificate.coupling Finset.univ (rayDegree rays{index}) (rayO rays{index} originDen{index}) (rayV rays{index} featureDen{index}) a + v{index} - countM{index} * F{index} a
noncomputable def origin{index} : ℝ :=
  SphereCertificate.origin Finset.univ (rayDegree rays{index}) (rayO rays{index} originDen{index}) - 2*countM{index}*v{index} - countM{index}^2*b{index}
''', 'end D4Bound.SphericalSurplusSign']
    text = '\n\n'.join(lines)+'\n'
    assert len(text.encode()) < 1024**2
    output = PKG/f'lean/D4Bound/SphericalSurplusSignData{index}.lean'
    if args.check:
        assert output.read_text() == text
    else:
        output.write_text(text)
    print(index,'nonzero rays',len(rays),'bytes',len(text))
