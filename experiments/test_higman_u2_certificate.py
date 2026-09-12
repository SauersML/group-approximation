"""Soundness controls for the finite U(2) polynomial certificate."""

from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from math import comb
import unittest

from higman_u2_certificate import (
    CERTIFICATE, INDICES, SIGNS, generate, initial_coefficients, polynomial,
    prod, split, verify,
)
from hs_word_certificate import Gaussian as Z, check, energy, evaluate
from higman_qutrit_witness import CANDIDATE


def power_value(p, x):
    return sum((c * prod(x[j] ** m[j] for j in range(4)) for m, c in p.items()), Q(0))


def bernstein_value(coefficients, t):
    return sum((c * prod(Q(comb(3, k[j])) * t[j] ** k[j] * (1-t[j]) ** (3-k[j])
                        for j in range(4))
                for k, c in zip(INDICES, coefficients)), Q(0))


def quaternion(parameters):
    norm = sum((v*v for v in parameters), Q(0))
    return ((1-norm)/(1+norm),) + tuple(2*v/(1+norm) for v in parameters)


def quaternion_matrix(q):
    w, x, y, z = q
    return ((Z(w, x), Z(y, z)), (Z(-y, z), Z(w, -x)))


def scale(a, scalar):
    return tuple(tuple(scalar*v for v in row) for row in a)


class HigmanU2CertificateTests(unittest.TestCase):
    def test_complete_certificate_and_reproducible_generation(self):
        certificate = json.loads(CERTIFICATE.read_text())
        result = verify(certificate)
        self.assertEqual(result['leaves'], 56)
        self.assertEqual(result['bernstein_coefficients_checked'], 14336)
        self.assertEqual(result['minimum_leaf_coefficient'], '1/36')
        self.assertFalse(result['proves_unrestricted_matrix_bound'])
        self.assertEqual(generate(), certificate)

    def test_power_conversion_and_piecewise_formula(self):
        t = (Q(1, 3), Q(2, 5), Q(3, 7), Q(4, 9))
        for signs in SIGNS:
            x = tuple(tj-1 if s < 0 else tj for s, tj in zip(signs, t))
            lower = sum((2-2*x[j] + 8*min(x[j], 0)*(1-x[(j-1)%4]**2)*(1-x[j]**2)
                         for j in range(4)), Q(0))
            value = power_value(polynomial(signs), x)
            self.assertEqual(value, 2*lower-(2-2*x[0]))
            self.assertEqual(value, bernstein_value(initial_coefficients(signs), t))

    def test_subdivision_preserves_polynomial_on_both_halves(self):
        b = initial_coefficients((-1, -1, 1, -1))
        t = (Q(1, 3), Q(2, 5), Q(3, 7), Q(4, 9))
        for axis in range(4):
            for side, child in enumerate(split(b, axis)):
                parent_t = list(t)
                parent_t[axis] = (t[axis]+side)/2
                self.assertEqual(bernstein_value(child, t), bernstein_value(b, parent_t))

    def test_reject_incomplete_invalid_and_uncertified_trees(self):
        certificate = json.loads(CERTIFICATE.read_text())
        cases = []
        c = deepcopy(certificate); c['orthants'].pop(); cases.append(c)
        c = deepcopy(certificate); c['orthants'][1] = c['orthants'][0]; cases.append(c)
        c = deepcopy(certificate); c['orthants'][0]['tree'] = None; cases.append(c)
        c = deepcopy(certificate); c['orthants'][0]['tree'][0] = True; cases.append(c)
        c = deepcopy(certificate); c['orthants'][0]['tree'].pop(); cases.append(c)
        c = deepcopy(certificate); c['matrix_dimension'] = 3; cases.append(c)
        c = deepcopy(certificate); c['coefficient'] = '16'; cases.append(c)
        for c in cases:
            with self.assertRaises(ValueError):
                verify(c)

    def test_quaternion_trace_and_cauchy_bound_against_word_products(self):
        qs = [quaternion(tuple(map(Q, p))) for p in
              ((1, 2, -1), (Q(1, 3), 0, 0), (0, 1, 1), (Q(3, 2), -1, 2))]
        matrices = [quaternion_matrix(q) for q in qs]
        # Exact word evaluation checks unitarity before the trace comparison.
        check(dict(CANDIDATE, coefficient='2'), matrices)
        for i, word in enumerate(CANDIDATE['relators']):
            j = (i+1) % 4
            xi, xj = qs[i][0], qs[j][0]
            dot = sum((a*b for a, b in zip(qs[i][1:], qs[j][1:])), Q(0))
            cross2 = (1-xi*xi)*(1-xj*xj)-dot*dot
            v = evaluate(matrices, word)
            self.assertEqual(sum(v[k][k].re for k in range(2))/2, xj-4*xj*cross2)
            lower = 2-2*xj+8*min(xj, 0)*(1-xi*xi)*(1-xj*xj)
            self.assertGreaterEqual(energy(v), lower)

    def test_scalar_phases_are_an_exact_convex_combination_of_signs(self):
        qs = [quaternion(tuple(map(Q, p))) for p in
              ((1, 0, 1), (0, 2, 0), (1, -1, 2), (0, 0, Q(1, 3)))]
        v = [quaternion_matrix(q) for q in qs]
        phases = [Z(Q(3, 5), Q(4, 5)), Z(Q(-5, 13), Q(12, 13)),
                  Z(0, 1), Z(-1, 0)]
        u = [scale(a, phase) for a, phase in zip(v, phases)]
        candidate = dict(CANDIDATE, coefficient='2')
        actual = Q(check(candidate, u)['strict_margin'])
        average = Q(0)
        for signs in product((-1, 1), repeat=4):
            weight = prod((Q(1)+s*p.re)/2 for s, p in zip(signs, phases))
            signed = [scale(a, Z(Q(s))) for a, s in zip(v, signs)]
            margin = Q(check(candidate, signed)['strict_margin'])
            self.assertLessEqual(margin, 0)
            average += weight*margin
        self.assertEqual(actual, average)
        self.assertLessEqual(actual, 0)


if __name__ == '__main__':
    unittest.main()
