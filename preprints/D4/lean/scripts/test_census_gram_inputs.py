"""Malformed-certificate regressions for exact Gram data generation."""
import copy
import unittest
from fractions import Fraction
from census_gram_inputs import (integer, rational, validate_kernel, vector, matrix,
                               validate_planes, RADIAL_ENDPOINTS)


def kernel_fixture():
    return {'common_denominator': '17', 'blocks': [{'rays': [
        {'weight': 1, 'vector': [0, i]+[0]*48} for i in range(34)]}]}


def plane_fixture():
    row = {'ray_count': 34, 'ray_centers': [0]*34,
           'physical_radial_linear_coefficients': [0]*49, 'constant': 0,
           'near_shell_lower_bounds': [0]*5, 'affine_count_coefficients': [0]*5,
           'pieces': [{'piece': i, 'physical_interval':
                       [str(x) for x in RADIAL_ENDPOINTS[i:i+2]],
                       'exact_restricted_Bernstein_coefficients': [0]*7,
                       'certified_lower_bound': 0} for i in range(7)]}
    return [copy.deepcopy(row) for _ in range(12)]


class ExactInputTests(unittest.TestCase):
    def test_nonintegral_integer_rejected(self):
        for value in ['3/2', Fraction(-1, 3), True, 1.0]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                integer(value)
        self.assertEqual(integer('12/3'), 4)

    def test_inexact_rational_rejected(self):
        for value in [False, 0.125]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                rational(value)
        self.assertEqual(rational('1/8'), Fraction(1, 8))

    def test_wrong_shapes_rejected(self):
        with self.assertRaises(ValueError):
            vector([1, 2], 3)
        with self.assertRaises(ValueError):
            matrix([[1, 2]], 1, 3)

    def test_valid_rays(self):
        validate_kernel(kernel_fixture())

    def test_malformed_rays_rejected(self):
        base = kernel_fixture()
        for kind in ['fractional_weight', 'negative_weight', 'fractional_vector',
                     'duplicate_key', 'missing_coordinate', 'zero_denominator']:
            bad = copy.deepcopy(base)
            rays = bad['blocks'][0]['rays']
            if kind == 'fractional_weight': rays[0]['weight'] = '3/2'
            elif kind == 'negative_weight': rays[0]['weight'] = -1
            elif kind == 'fractional_vector': rays[0]['vector'][4] = '3/2'
            elif kind == 'duplicate_key': rays[1]['vector'][1] = rays[0]['vector'][1]
            elif kind == 'missing_coordinate': rays[0]['vector'].pop()
            else: bad['common_denominator'] = 0
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                validate_kernel(bad)

    def test_plane_schema_rejects_bad_intervals_and_counts(self):
        base = plane_fixture()
        validate_planes(base)
        for kind in ['missing_plane', 'wrong_count_width', 'wrong_interval',
                     'duplicate_piece', 'inexact_center']:
            bad = copy.deepcopy(base)
            if kind == 'missing_plane': bad.pop()
            elif kind == 'wrong_count_width': bad[0]['affine_count_coefficients'].pop()
            elif kind == 'wrong_interval': bad[0]['pieces'][0]['physical_interval'][1] = '3/2'
            elif kind == 'duplicate_piece': bad[0]['pieces'][1]['piece'] = 0
            else: bad[0]['ray_centers'][0] = 0.125
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                validate_planes(bad)


if __name__ == '__main__':
    unittest.main()
