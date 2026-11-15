"""Exact affine products with checked common-factor removal and envelopes.

No sampled inequalities or external verdicts enter the Lean statements. Each
integer identity is checked in Lean and the real interpretation uses the proved
Bernstein partition and nonnegative basis.
"""
from pathlib import Path
import argparse
import ast
import math
import numpy as np

PKG = Path(__file__).resolve().parents[2]
OUT = PKG / 'lean/D4Bound'
ap = argparse.ArgumentParser()
ap.add_argument('--check', action='store_true')
ap.add_argument('--index', type=int, choices=range(3), required=True)
args = ap.parse_args()
COLS_PER_MODULE = 6
n = args.index
p, q = [(751467, 500000), (61, 40), (303, 200)][n]


def readvalue(text, marker):
    return ast.literal_eval(text.split(marker)[1].split('\n\n')[0].replace('![', '['))


def vec(value):
    if isinstance(value, np.ndarray):
        value = value.tolist()
    return '![' + ', '.join(vec(x) if isinstance(x, list) else str(int(x)) for x in value) + ']'


def emit(name, lines):
    text = '\n\n'.join(lines) + '\n'
    assert len(text.encode()) < 1024**2, (name, len(text))
    path = OUT / (name + '.lean')
    if args.check:
        assert path.read_text() == text
    else:
        path.write_text(text)
    print(name, len(text))


header = ['set_option maxHeartbeats 0', 'set_option maxRecDepth 20000',
          'set_option Elab.async false', 'namespace D4Bound.SphericalSurplusSign.Bernstein16']
power = (OUT / f'SphericalSurplusSignPower{n}Data.lean').read_text()
affine = (OUT / f'SphericalSurplusSignAffine{n}.lean').read_text()
tree = (OUT / f'SphericalSurplusSignTreeData{n}.lean').read_text()
P = np.array(readvalue(power, f'def repairPower{n} : Tensor := '), dtype=object)
den = int(readvalue(power, f'def repairDen{n} : ℤ := '))
T = np.array(readvalue(affine, f'def affine{n} : I → I → ℤ := '), dtype=object)
td = int(readvalue(affine, f'def affineDen{n} : ℤ := '))
prev = f'repairPower{n}'
previous = f'SphericalSurplusSignPower{n}Data'
factors = []
for axis, label in [(2, 'Z'), (1, 'Y'), (0, 'X')]:
    moved = np.moveaxis(P, axis, 0)
    P = np.moveaxis((T @ moved.reshape(17, -1)).reshape(moved.shape), 0, axis)
    factor = math.gcd(*(int(v) for v in P.flat))
    assert factor > 0
    factors.append(factor)
    P //= factor
    name = f'SphericalSurplusSignTransform{n}{label}'
    value = f'transform{n}{label}'
    scale = f'transformFactor{n}{label}'
    lines = [f'import D4Bound.{previous}', f'import D4Bound.SphericalSurplusSignAffine{n}',
             'import D4Bound.SphericalSurplusSignScaledTransform16'] + header
    definitions = [f'def {value} : Tensor := {vec(P)}', f'def {scale} : ℤ := {factor}']
    if label == 'X':
        # The final-axis tensor is dense. Its literal lives in a data module.
        # A row i of matrixX reads prev a j k for every a, j, k (the whole
        # input tensor), so one row check exceeded the 4 GiB guard. Each
        # check here fixes the first two indices (i, j) and reads only
        # prev a j k for fixed j. Columns are grouped into modules.
        data_name = name + 'Data'
        emit(data_name, ['import D4Bound.SphericalSurplusSignTensor16'] + header
             + definitions + ['end D4Bound.SphericalSurplusSign.Bernstein16'])
        groups = [list(range(g, min(g + COLS_PER_MODULE, 17))) for g in range(0, 17, COLS_PER_MODULE)]
        for g, cols in enumerate(groups):
            part = [f'import D4Bound.{data_name}', f'import D4Bound.{previous}'] + header
            for j in cols:
                # One small kernel check per entry line (i, j): the module's
                # peak is its import footprint plus the largest single check.
                for i in range(17):
                    part.append(f'''theorem {value}_c{j}_r{i} : ∀ k,
    matrixX affine{n} {prev} {i} {j} k = scaleTensor {scale} {value} {i} {j} k := by decide +kernel''')
                part.append(f'''theorem {value}_col{j} : ∀ i k,
    matrixX affine{n} {prev} i {j} k = scaleTensor {scale} {value} i {j} k := by
  intro i k
  fin_cases i
''' + '\n'.join(f'  · exact {value}_c{j}_r{i} k' for i in range(17)))
            part += [f'#print axioms {value}_col{cols[0]}', 'end D4Bound.SphericalSurplusSign.Bernstein16']
            emit(f'{name}Col{g}', part)
        lines = [f'import D4Bound.{name}Col{g}' for g in range(len(groups))] + header
        lines.append(f'''theorem {value}_eq : matrixX affine{n} {prev} = scaleTensor {scale} {value} := by
  funext i j k
  fin_cases j
''' + '\n'.join(f'  · exact {value}_col{j} i k' for j in range(17)))
        lines += [f'#print axioms {value}_eq', 'end D4Bound.SphericalSurplusSign.Bernstein16']
        emit(name, lines)
        prev, previous = value, name
        continue
    lines += definitions
    for i in range(17):
        lines.append(f'''theorem {value}_row{i} : ∀ j k,
    matrix{label} affine{n} {prev} {i} j k = scaleTensor {scale} {value} {i} j k := by decide +kernel''')
    lines.append(f'''theorem {value}_eq : matrix{label} affine{n} {prev} = scaleTensor {scale} {value} := by
  funext i j k
  fin_cases i
''' + '\n'.join(f'  · exact {value}_row{i} j k' for i in range(17)))
    lines += [f'#print axioms {value}_eq', 'end D4Bound.SphericalSurplusSign.Bernstein16']
    emit(name, lines)
    prev, previous = value, name

U = np.array(readvalue(tree, f'def upper{n} : Tensor := '), dtype=object)
precision = int(readvalue(tree, f'def precision{n} : ℕ := '))
factor = math.prod(factors)
D = den * td**3
for x, y in zip(P.flat, U.flat):
    assert -((-int(x) * factor * 2**precision) // D) == int(y)
factor_expr = f'transformFactor{n}Z*transformFactor{n}Y*transformFactor{n}X'
lines = [f'import D4Bound.{previous}', f'import D4Bound.SphericalSurplusSignPower{n}',
         f'import D4Bound.SphericalSurplusSignTreeData{n}'] + header
for i in range(17):
    lines.append(f'''theorem upper{n}_matrix_row{i} : ∀ j k,
    (2^precision{n}:ℤ)*(({factor_expr})*transform{n}X {i} j k) ≤
      (repairDen{n}*affineDen{n}^3)*upper{n} {i} j k := by decide +kernel''')
lines.append(f'''theorem upper{n}_matrix_coeff : ∀ i j k,
    (2^precision{n}:ℤ)*(({factor_expr})*transform{n}X i j k) ≤
      (repairDen{n}*affineDen{n}^3)*upper{n} i j k := by
  intro i j k
  fin_cases i
''' + '\n'.join(f'  · exact upper{n}_matrix_row{i} j k' for i in range(17)))
lines.append(f'''theorem upper{n}_power_correct {{x y z : ℝ}}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision{n}:ℝ)*powerEv repairPower{n}
      (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z) ≤
        (repairDen{n}:ℝ)*ev upper{n} x y z := by
  have hc : ∀ i j k, (2^precision{n}:ℤ)*
      (matrixX affine{n} (matrixY affine{n} (matrixZ affine{n} repairPower{n}))) i j k ≤
        (repairDen{n}*affineDen{n}^3)*upper{n} i j k := by
    rw [matrixXYZ_scaled affine{n} repairPower{n} transform{n}Z transform{n}Y transform{n}X
      transformFactor{n}Z transformFactor{n}Y transformFactor{n}X
      transform{n}Z_eq transform{n}Y_eq transform{n}X_eq]
    exact upper{n}_matrix_coeff
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    upper_from_matrix affine{n} repairPower{n} upper{n} affineDen{n} repairDen{n}
      (2^precision{n}) (by norm_num [affineDen{n}]) hc
      (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z) x y z
      (fun j => affine{n}_exact j x) (fun j => affine{n}_exact j y)
      (fun j => affine{n}_exact j z) hx hx1 hy hy1 hz hz1''')
raw = f'''(kernel{n} (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z)+
      kernel{n} (-1+({p}:ℝ)/{q}*x) (-1+({p}:ℝ)/{q}*z) (-1+({p}:ℝ)/{q}*y)+
      kernel{n} (-1+({p}:ℝ)/{q}*y) (-1+({p}:ℝ)/{q}*z) (-1+({p}:ℝ)/{q}*x)-3*(epsilon{n}:ℝ))'''
lines.append(f'''theorem upper{n}_raw_correct {{x y z : ℝ}}
    (hx : 0≤x) (hx1 : x≤1) (hy : 0≤y) (hy1 : y≤1) (hz : 0≤z) (hz1 : z≤1) :
    (2^precision{n}:ℝ)*{raw} ≤ ev upper{n} x y z := by
  have hb := upper{n}_power_correct hx hx1 hy hy1 hz hz1
  rw [repairPower{n}_correct] at hb
  have hd : (0:ℝ)<repairDen{n} := by norm_num [repairDen{n}]
  have hh : (repairDen{n}:ℝ)*((2^precision{n}:ℝ)*{raw}-ev upper{n} x y z)≤0 := by nlinarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh hd)''')
lines += [f'#print axioms upper{n}_raw_correct', 'end D4Bound.SphericalSurplusSign.Bernstein16']
emit(f'SphericalSurplusSignUpper{n}', lines)
print('PASS exact transforms and ceilings; all emitted proof obligations need Lean compilation.')
