"""Regression checks for degree signs, word order, and the proof boundary."""
from fractions import Fraction as Q
import unittest

from nonsingular_equation_audit import (
    degree_case, diagonal, energy, exponent_sum, freely_reduce, identity,
    inverse_word, nonsingular_exponent, power_fiber, power_word, root_packet,
    word_value,
)


class NonsingularEquationTests(unittest.TestCase):
    def test_degree_uses_rank_and_negative_power_orientation(self):
        self.assertEqual(degree_case(3, 2)["signed_count"], 8)
        self.assertEqual(degree_case(3, -2)["signed_count"], -8)
        self.assertEqual(degree_case(2, -2)["signed_count"], 4)
        target, roots = power_fiber(1, -2)
        self.assertEqual(target, (Q(1, 2),))
        self.assertEqual(set(roots), {(Q(1, 4),), (Q(3, 4),)})

    def test_zero_exponent_cannot_enter_the_root_theorem(self):
        singular = (2, 1, -2)
        self.assertEqual(exponent_sum(singular, 2), 0)
        with self.assertRaises(ValueError):
            nonsingular_exponent(singular, 2)
        with self.assertRaises(ValueError):
            power_fiber(2, 0)
        with self.assertRaises(ValueError):
            exponent_sum((1, 0), 2)

    def test_inverse_encoding_reverses_order_and_exponent(self):
        word = (1, 2, -1, 2, -3, 2)
        self.assertEqual(inverse_word(word), (-2, 3, -2, 1, -2, -1))
        self.assertEqual(exponent_sum(inverse_word(word), 2), -3)
        self.assertEqual(freely_reduce(word + inverse_word(word)), ())

    def test_exact_noncommuting_root_preserves_old_involutions(self):
        for m in (-3, -2, -1, 1, 2, 3):
            generators, word = root_packet(3, m)
            self.assertEqual(word_value(generators, word), identity(3))
            self.assertEqual(word_value(generators, (1, 1)), identity(3))
            self.assertEqual(word_value(generators, (2, 2)), identity(3))
            self.assertEqual(energy(generators[0]), Q(8, 3))
            self.assertGreater(energy(word_value(generators, (1, 5, -1, -5))), 0)
        generators, _ = root_packet(3, 1)
        falsely_commuted = (1, 2, 3, 4) + power_word(5, 1)
        self.assertNotEqual(word_value(generators, falsely_commuted), identity(3))

    def test_singular_equation_really_kills_a_nontrivial_coefficient(self):
        w = (2, 1, -2)
        self.assertEqual(freely_reduce((-2,) + w + (2,)), (1,))
        a = diagonal((-1, -1))
        t = root_packet(2, 1)[0][-1]
        self.assertEqual(word_value((a, t), (1, 1)), identity(2))
        self.assertEqual(word_value((a, t), w), a)
        self.assertNotEqual(a, identity(2))

    def test_a_chosen_root_does_not_guarantee_a_faithful_extension(self):
        for root in (identity(1), diagonal((-1,))):
            self.assertEqual(word_value((root,), (1, 1)), identity(1))
        self.assertEqual(energy(identity(1)), 0)
        self.assertEqual(energy(diagonal((-1,))), 4)


if __name__ == "__main__":
    unittest.main()
