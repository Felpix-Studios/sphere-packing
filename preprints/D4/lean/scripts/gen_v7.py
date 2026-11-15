"""Generate exact V7 data definitions, retaining the certificate coefficients.

--check compares the generated text with the included Lean source. The only
structural changes are removal of zero origin coordinates in Gram rays and
expansion of upper-triangle count coefficients to symmetric matrices.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
DATA = HERE.parents[1] / 'data/v7'


def rat(x):
    if isinstance(x, bool) or not isinstance(x, (str, int, Q)):
        raise ValueError('not exact')
    return Q(x)


def q(x):
    a = rat(x)
    return str(a.numerator) if a.denominator == 1 else f'({a.numerator} / {a.denominator} : ℚ)'


def integer(x, minimum=0):
    a = rat(x)
    if a.denominator != 1 or a < minimum:
        raise ValueError('expected an integral coefficient in the declared range')
    return a.numerator


def arr(xs, fn=q):
    return '[' + ', '.join(fn(x) for x in xs) + ']'


def rec(*args):
    return '⟨' + ', '.join(args) + '⟩'


def gen():
    kd, od, sd, gd = [json.loads((DATA / n).read_text()) for n in
                      ['kernel.json', 'origin.json', 'scalar.json', 'graph_energies.json']]
    assert tuple(integer(kd[k]) for k in ['dimension', 'local_degree', 'angular_degree']) == (4, 6, 18)
    assert integer(sd['dimension']) == 4
    assert rat(sd['alpha']) == 2 and rat(sd['cutoff']) == Q(7, 4)
    assert integer(kd['common_denominator'], 1) > 0
    assert len(kd['blocks']) == 19 and len(kd['breaks']) == 8
    br = list(map(rat, kd['breaks']))
    assert br[0] == 1 and br[-1] == Q(7, 4) and all(a < b for a, b in zip(br, br[1:]))
    assert len(kd['radial_basis_intervals']) == 7
    assert all(rat(a) <= br[i] < br[i+1] <= rat(b)
               for i, (a, b) in enumerate(kd['radial_basis_intervals']))
    assert len(od['v']) == 49
    assert all(len(c['w']) == 49 for c in od['pointed_caps'] + od['pointed_tents'] +
               od['independent_antipodal_allocations'])
    assert all(rat(c['sigma']) == -1 for c in od['pointed_tents'])
    assert all(rat(c['pair_coefficient']) == 23 and rat(c['mixed_kernel_coefficient']) == Q(-1, 2)
               for c in od['conditional_radial_rays'])
    assert all(c['scalar_basis'] == 'U_j(t)/(j+1)' for c in od['appended_spherical_local_energy_rays'])
    assert od['full_pair_count_gauge']['gauge'] == 'indicator_over_count_bound'
    assert integer(od['full_pair_count_gauge']['count_bound'], 2) == 24
    out = ['import Mathlib.Data.Rat.Cast.Order\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 4096\n\nnamespace D4Bound.V7\n']
    out += ['''structure Ray where
  weight : ℚ
  vector : List ℚ

structure Cap where
  d : ℚ
  a2 : ℚ
  sigma : ℚ
  multiplicity : ℚ
  weight : ℚ
  vector : List ℚ
  cutoff : Option ℚ

structure Tent where
  d : ℚ
  capacity : ℚ
  weight : ℚ
  vector : List ℚ

structure AllocationData where
  weight : ℚ
  vector : List ℚ
  twoLevel : Bool
  inner : ℚ
  outer : ℚ

structure ConditionalRay where
  inner : ℚ
  outer : ℚ
  weight : ℚ

structure CountPolynomial where
  radii : List ℚ
  weight : ℚ
  constant : ℚ
  linear : List ℚ
  matrix : List (List ℚ)

structure SphericalRay where
  radius : ℚ
  weight : ℚ
  bound : ℚ
  coefficients : List ℚ

structure Graph where
  weight : ℚ
  capacity : ℚ
  lo1 : ℚ
  hi1 : ℚ
  lo2 : ℚ
  hi2 : ℚ
  tlo : ℚ
  thi : ℚ
  firstOpen : Bool
  mixed : Bool
''']

    def emit(name, typ, expr):
        out.append(f'def {name} : {typ} := {expr}\n')

    emit('breaks', 'List ℚ', arr(kd['breaks']))
    emit('basisIntervals', 'List (ℚ × ℚ)', arr(kd['radial_basis_intervals'],
         lambda a: '(' + q(a[0]) + ', ' + q(a[1]) + ')'))
    emit('gramDenominator', 'ℚ', q(kd['common_denominator']))
    blocks = []
    for ell, b in enumerate(kd['blocks']):
        rays = []
        for ray in b['rays']:
            assert type(ray['weight']) is int and ray['weight'] > 0
            v = ray['vector']
            assert all(type(x) is int for x in v)
            if ell == 0:
                assert v[0] == 0
                v = v[1:]
            assert len(v) == 49
            rays.append(rec(q(ray['weight']), arr(v)))
        name = 'gramRays' + str(ell)
        emit(name, 'List Ray', arr(rays, str))
        blocks.append(name)
    emit('gramRays', 'List (List Ray)', arr(blocks, str))
    emit('originVector', 'List ℚ', arr(od['v']))
    emit('gramOrigin', 'ℚ', q(od['kappa']))
    caps = []
    for c in od['pointed_caps']:
        integer(c['M'])
        cut = 'none' if 'pivot_lower_cutoff' not in c else '(some ' + q(c['pivot_lower_cutoff']) + ')'
        caps.append(rec(q(c['d']), q(c['a2']), q(c['sigma']), q(c['M']),
                        q(c['weight']), arr(c['w']), cut))
    emit('caps', 'List Cap', arr(caps, str))
    emit('tents', 'List Tent', arr(od['pointed_tents'], lambda c:
         rec(q(c['d']), q(c['capacity']), q(c['weight']), arr(c['w']))))
    alloc = []
    for a in od['independent_antipodal_allocations']:
        assert rat(a['origin_constant']) == 0
        two = a['capacity_profile'] == 'two_level'
        assert a['capacity_profile'] in ['two_level', 'classical_improvement']
        if two:
            assert a['inner_boundary'] == 'strict' and a['outer_boundary'] == 'closed'
        alloc.append(rec(q(a['weight']), arr(a['w']), str(two).lower(),
                         q(a.get('inner_radius', 0)), q(a.get('outer_radius', 0))))
    emit('allocations', 'List AllocationData', arr(alloc, str))
    emit('conditionalRays', 'List ConditionalRay', arr(od['conditional_radial_rays'], lambda c:
         rec(q(c['inner_radius']), q(c['outer_radius']), q(c['weight']))))
    counts = [dict(od['nested_count_quadratic'], weight=1)] + od['conditional_count_polynomials']
    cr = []
    for c in counts:
        n = len(c['radii'])
        coeff = c['coefficients']
        assert len(coeff) == 1+n+n*(n+1)//2
        mat = [[Q(0)]*n for _ in range(n)]
        idx = 1+n
        for i in range(n):
            for j in range(i, n):
                mat[i][j] = mat[j][i] = rat(coeff[idx])
                idx += 1
        cr.append(rec(arr(c['radii']), q(c['weight']), q(coeff[0]),
                      arr(coeff[1:1+n]), arr(mat, arr)))
    emit('countPolynomials', 'List CountPolynomial', arr(cr, str))
    emit('sphericalRays', 'List SphericalRay', arr(od['appended_spherical_local_energy_rays'], lambda c:
         rec(q(c['R']), q(c['weight']), q(c['B']), arr(c['scalar_coefficients']))))
    graphs = [
        (gd['weights'][0], 862, 1, '103/100', '103/100', '3/2', '-4/5', '-1/2', True, True),
        (gd['weights'][1], 1102, 1, '103/100', '3/2', '7/4', '-19/20', '-3/4', False, True),
        (gd['weights'][2], 1358, '33/28', '7/4', '33/28', '7/4', -1, '-7/8', False, False),
        (gd['outer_graph_weight'], 120, 1, '103/100', 1, '103/100', -1, '-3/4', False, False),
        (gd['narrow_graph_weight'], 604, '33/28', '7/4', '33/28', '7/4', -1, '-183/200', False, False),
        (gd['moderate_graph_weight'], 1880, '7/5', '3/2', '7/5', '3/2', '-4/5', '-11/20', False, False)]
    emit('graphs', 'List Graph', arr(graphs, lambda g:
         rec(*([q(v) for v in g[:8]] + [str(v).lower() for v in g[8:]]))))
    emit('gaugeRadius', 'ℚ', q(od['full_pair_count_gauge']['radius']))
    emit('gaugeCount', 'ℚ', q(od['full_pair_count_gauge']['count_bound']))
    out.append('end D4Bound.V7\n')
    return '\n'.join(out)


parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
target = HERE.parent / 'D4Bound/V7Data.lean'
text = gen()
if args.check:
    if target.read_text() != text:
        raise SystemExit('FAIL: V7Data.lean differs from JSON-derived exact data')
    print('PASS: exact V7 data source matches JSON')
else:
    target.write_text(text)
    print(target)
