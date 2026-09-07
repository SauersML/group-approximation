"""Regression checks for dimension normalization and sharp padding examples."""
from fractions import Fraction as Q
import unittest

from flexible_hs_metric_audit import (
    compression_terms, diagonal, diagonal_identity_distance_squared,
    distance_squared, extend, identity, require_unitary,
    sharp_family_formula, sqrt_triangle_holds, word_value,
)


class FlexibleHSMetricTests(unittest.TestCase):
    def test_common_normalization_is_not_the_smaller_internal_defect(self):
        a, b = diagonal([-1, 1]), identity(2)
        x, y = diagonal([-1]), identity(1)
        self.assertEqual(distance_squared(a, b), 2)
        self.assertEqual(distance_squared(x, y), 4)
        self.assertEqual(distance_squared(extend(x, 2), extend(y, 2)), 2)
        self.assertEqual(distance_squared(a, x), Q(1, 2))
        self.assertEqual(distance_squared(b, y), Q(1, 2))

    def test_empty_word_keeps_its_dimension_charge(self):
        small, large = (identity(1),), (identity(3),)
        self.assertEqual(distance_squared(word_value(small, ()), word_value(large, ())), Q(2, 3))

    def test_compression_identity_keeps_off_diagonal_leakage(self):
        rotation = ((Q(3, 5), Q(-4, 5)), (Q(4, 5), Q(3, 5)))
        terms = compression_terms(identity(1), rotation)
        self.assertEqual(terms, (Q(1, 2), Q(2, 25), Q(8, 25)))
        self.assertEqual(sum(terms), distance_squared(identity(1), rotation))

    def test_factor_two_is_attained_by_the_trivial_representation_class(self):
        entries = (1, 1, 1, 1, -1)
        values = {n: diagonal_identity_distance_squared(entries, n) for n in range(1, 51)}
        self.assertEqual(min(values.values()), Q(1, 5))
        self.assertEqual(min(value for n, value in values.items() if n >= 5), Q(4, 5))
        for n, actual in values.items():
            self.assertEqual(actual, sharp_family_formula(5, 1, n))

    def test_exact_triangle_decision_rejects_a_false_bound(self):
        self.assertTrue(sqrt_triangle_holds(Q(1), Q(1), Q(4)))
        self.assertTrue(sqrt_triangle_holds(Q(1, 2), Q(1, 3), Q(1, 4)))
        self.assertFalse(sqrt_triangle_holds(Q(1), Q(1), Q(9)))
        with self.assertRaises(ValueError):
            sqrt_triangle_holds(Q(-1), Q(1), Q(1))

    def test_corrupted_matrix_cannot_enter_the_unitary_sample(self):
        with self.assertRaises(ValueError):
            require_unitary(((Q(2), Q(0)), (Q(0), Q(1))))


if __name__ == "__main__":
    unittest.main()
