"""Regression tests for the mathematical certificate replay boundary."""

import copy
import unittest

import finite_context_energy_audit as audit


class CertificateTests(unittest.TestCase):
    def test_free_reduction_does_not_commute_generators(self):
        self.assertEqual(audit.reduce_word((1, 2, -2, -1)), ())
        self.assertEqual(audit.reduce_word((1, 2, -1, -2)), (1, 2, -1, -2))
        self.assertNotEqual(audit.mul({(1,): 1}, {(2,): 1}),
                            audit.mul({(2,): 1}, {(1,): 1}))

    def test_inverse_sign_and_empty_certificates(self):
        examples = audit.sample_certificates()
        self.assertTrue(all(x["identity_verified"] for x in examples))
        self.assertEqual(examples[0]["constant"], 0)
        self.assertEqual(examples[2]["word"], [2, 1, -2, -1])
        self.assertEqual(examples[3]["square_count"], 3)
        self.assertEqual(examples[4]["word"], [])

    def test_false_word_and_wrong_sign_are_rejected(self):
        r = (1, 2, -1, -2)
        with self.assertRaisesRegex(ValueError, "not the supplied product"):
            audit.normal_closure_certificate((1,), [(r, (), 1)])
        with self.assertRaisesRegex(ValueError, "not the supplied product"):
            audit.normal_closure_certificate(r, [(r, (), -1)])
        with self.assertRaisesRegex(ValueError, "invalid relator sign"):
            audit.normal_closure_certificate(r, [(r, (), True)])

    def test_star_reverses_multiplication(self):
        a = {(): 2, (1,): -3, (1, 2): 1}
        b = {(-1, 2): 4, (2,): -1}
        self.assertEqual(audit.star(audit.mul(a, b)),
                         audit.mul(audit.star(b), audit.star(a)))


class WitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.witness = audit.build_witness()

    def test_finite_vector_conditions_do_not_claim_global_relators(self):
        result = audit.verify_witness(self.witness)
        self.assertTrue(result["all_context_defect_vectors_zero"])
        self.assertEqual(result["target_displacement_squared"], 2)
        self.assertFalse(result["global_relators_are_exact"])
        self.assertTrue(all(n > 0 for n in result["global_relator_moved_points"]))

    def test_nonbijective_and_wrong_internal_edges_are_rejected(self):
        bad = copy.deepcopy(self.witness)
        bad["permutations"][0][0] = bad["permutations"][0][1]
        with self.assertRaisesRegex(ValueError, "not a permutation"):
            audit.verify_witness(bad)
        bad = copy.deepcopy(self.witness)
        bad["permutations"][0] = list(range(len(bad["points"])))
        with self.assertRaisesRegex(ValueError, "internal edge"):
            audit.verify_witness(bad)

    def test_insufficient_context_radius_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "too short"):
            audit.verify_witness(audit.build_witness(1))


if __name__ == "__main__":
    unittest.main()
