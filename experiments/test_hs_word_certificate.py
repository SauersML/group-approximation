"""Mathematical and malformed-witness controls for the exact HS refuter."""

from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

from hs_word_certificate import (
    Gaussian as Z, ZERO, ONE, adjoint, candidate, cayley, check, decode_matrix,
    encode_matrix, energy, evaluate, identity, integer_vectors, multiply, search,
)


class ExactWordCertificateTests(unittest.TestCase):
    def test_pauli_commutator_and_inverse(self):
        x = ((ZERO, ONE), (ONE, ZERO))
        z = ((ONE, ZERO), (ZERO, -ONE))
        self.assertEqual(evaluate([x, z], [1, 2, -1, -2]),
                         ((-ONE, ZERO), (ZERO, -ONE)))
        c = {"generators": ["x", "z"], "relators": [[1, 1], [2, 2]],
             "word": [1, 2, -1, -2], "coefficient": "1000000"}
        result = check(c, [x, z])
        self.assertEqual(result["strict_margin"], "4")
        self.assertEqual(result["relator_energy_sum"], "0")

    def test_cayley_complex_and_trace_identity(self):
        a = cayley([Q(1, 3), Q(-2, 5), Q(3, 7), Q(4, 9)], 2)
        self.assertEqual(multiply(adjoint(a), a), identity(2))
        self.assertEqual(energy(a), 2 - sum(a[j][j].re for j in range(2)))
        self.assertEqual(decode_matrix(encode_matrix(a)), a)

    def test_strict_boundary_and_normalization(self):
        c = {"generators": ["a"], "relators": [[1]], "word": [1], "coefficient": 1}
        scalar = ((Z(Q(0), Q(1)),),)
        self.assertEqual(check(c, [scalar])["status"], "no_violation_at_tuple")
        padded = ((Z(Q(0), Q(1)), ZERO), (ZERO, ONE))
        self.assertEqual(energy(padded), energy(scalar) / 2)

    def test_reject_nonunitary_and_inexact_input(self):
        c = {"generators": ["a"], "relators": [], "word": [1], "coefficient": 1}
        with self.assertRaises(ValueError):
            check(c, [((Z(Q(2)),),)])
        for value in (0.5, True):
            with self.assertRaises(ValueError):
                decode_matrix([[[value, 0]]])
        for word in ([0], [2], [True]):
            with self.assertRaises(ValueError):
                candidate(dict(c, word=word))

    def test_search_witness_replays_and_no_witness_is_inconclusive(self):
        c = {"generators": ["a"], "relators": [], "word": [1], "coefficient": 1}
        found = search(c, 10, 1, 1)
        self.assertEqual(found["verification"]["status"], "counterexample")
        self.assertEqual(check(found["candidate"], [decode_matrix(a) for a in found["matrices"]]),
                         found["verification"])
        c["relators"] = [[1]]
        absent = search(c, 10, 1, 1)
        self.assertEqual(absent["status"], "inconclusive")
        self.assertFalse(absent["proves_all_dimensions"])

    def test_l1_enumeration_is_complete_on_small_ball(self):
        vectors = set(integer_vectors(2, 2))
        expected = {(a, b) for a in range(-2, 3) for b in range(-2, 3)
                    if abs(a) + abs(b) <= 2}
        self.assertEqual(vectors, expected)
        self.assertEqual(list(integer_vectors(1200, 0)), [(0,) * 1200])

    def test_committed_higman_witness_and_independent_trace_formula(self):
        path = Path(__file__).resolve().parents[1] / 'research/artifacts/higman-hs-word-coefficient-witness.json'
        data = json.loads(path.read_text())
        matrices = [decode_matrix(a) for a in data['matrices']]
        result = check(data['candidate'], matrices)
        x, y = Q(-60, 109), Q(12, 37)
        total = 4 - 2*y - 2*x*(4*x*x - 3) - 8*x*(1-x*x)*y*y
        self.assertEqual(Q(result['word_energy']), 2 - 2*x)
        self.assertEqual(Q(result['relator_energy_sum']), total)
        self.assertEqual(result['strict_margin'], '270418822/8864473505')
        self.assertEqual(result, data['verification'])
        padded = [tuple(tuple(a[i][j] if i < 2 and j < 2 else
                             ONE if i == j else ZERO for j in range(3))
                        for i in range(3)) for a in matrices]
        diluted = check(data['candidate'], padded)
        self.assertEqual(Q(diluted['strict_margin']), Q(2, 3) * Q(result['strict_margin']))
        self.assertEqual(Q(diluted['word_energy']), Q(2, 3) * Q(result['word_energy']))


if __name__ == "__main__":
    unittest.main()
