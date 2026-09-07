"""Regression checks for exact lifted traces, including misleading zero residues."""

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from kaplansky_trace_certificate import (
    FiniteGroup, MatrixGroupRing, bundle, certify, cyclic_table,
    detection_precision, example_specs, reduced,
)


class TraceCertificateTests(unittest.TestCase):
    def test_leavitt_pair_only_separates_after_lifting(self):
        cases = [certify(s) for s in example_specs()[:3]]
        self.assertEqual([c["status"] for c in cases],
                         ["inconclusive", "obstructed", "obstructed"])
        self.assertEqual([(c["e"]["trace"], c["f"]["trace"]) for c in cases],
                         [(0, 0), (2, 0), (22, 4)])
        self.assertTrue(all(c["strictly_nested"] for c in cases))

    def test_sharp_scalar_family_for_two_primes(self):
        for spec in example_specs():
            if not spec["name"].startswith("cyclic_"):
                continue
            with self.subTest(name=spec["name"]):
                certificate = certify(spec)
                p, k, m = spec["p"], spec["precision"], len(spec["group"]["table"])
                expected = ((m - 1) * pow(m, -1, p ** k)) % (p ** k)
                self.assertEqual(certificate["trace_difference"], expected)
                self.assertEqual(certificate["e"]["regular_rank"], m - 1)
                bound = detection_precision(p, 1, m)
                self.assertEqual(certificate["status"],
                                 "obstructed" if k == bound else "inconclusive")

    def test_exhaustive_f2_s3_idempotents_against_regular_rank(self):
        # p divides |S3|: cancellation in the rank ratio is essential.
        spec = next(s for s in example_specs() if s["name"] == "s3_conjugate_averages")
        group = FiniteGroup(spec["group"]["table"])
        ring = MatrixGroupRing(group, 2, 4, 1)
        seen = 0
        for coefficients in product(range(2), repeat=6):
            terms = [[0, 0, g, c] for g, c in enumerate(coefficients)]
            a = ring.from_terms(terms)
            if reduced(ring.mul(a, a), 2) != a:
                continue
            seen += 1
            candidate = {**spec, "p": 2, "precision": 4, "e": terms, "f": []}
            certificate = certify(candidate)
            rank = certificate["e"]["regular_rank"]
            self.assertEqual(rank % 2, 0)
            self.assertEqual(certificate["e"]["trace"],
                             ((rank // 2) * pow(3, -1, 16)) % 16)
            if a:
                self.assertEqual(certificate["status"], "obstructed")
        self.assertGreater(seen, 2)

    def test_matrix_lift_independence_with_noncommuting_coefficients(self):
        spec = next(s for s in example_specs() if s["name"] == "s3_conjugate_averages")
        group = FiniteGroup(spec["group"]["table"])
        ring = MatrixGroupRing(group, 3, 5, 2)
        # Different transposition averages occupy the two diagonal entries.
        diagonal = ring.from_terms(spec["e"] + [[1, 1, g, c]
                                                for _, _, g, c in spec["f"]])
        shear = ring.from_terms([[0, 1, 3, 1]])
        u = ring.add(ring.identity(), shear)
        v = ring.add(ring.identity(), ring.scale(-1, shear))
        self.assertEqual(ring.mul(u, v), ring.identity())
        conjugate = ring.mul(ring.mul(u, diagonal), v)
        # Arbitrary changes of coefficient lifts, including off-diagonal terms.
        perturbation = ring.from_terms([[0, 0, 2, 3], [1, 0, 4, 6], [1, 1, 1, -3]])
        for original in (diagonal, conjugate, ring.add(conjugate, perturbation)):
            with self.subTest(original=original):
                lifted, rounds = ring.lift(original)
                self.assertEqual(rounds, 3)
                self.assertEqual(ring.trace(lifted), 1)  # 1/2 + 1/2.
                self.assertEqual(ring.mul(lifted, lifted), lifted)

    def test_equal_traces_never_assert_equivalence(self):
        for name in ("s3_conjugate_averages", "c2_distinct_characters_equal_trace"):
            spec = next(s for s in example_specs() if s["name"] == name)
            self.assertEqual(certify(spec)["status"], "inconclusive")
        # For C2 in characteristic 3, the two character projectives are
        # nonisomorphic over that group algebra, despite equal normalized rank.

    def test_integer_precision_bound_with_p_part_removed(self):
        self.assertEqual(detection_precision(2, 1, 8), 1)
        self.assertEqual(detection_precision(2, 1, 9), 4)
        self.assertEqual(detection_precision(2, 4, 1), 3)
        self.assertEqual(detection_precision(3, 1, 10), 3)

    def test_invalid_inputs_fail(self):
        base = example_specs()[0]
        for key, value in (("p", 4), ("p", True), ("precision", 0),
                           ("matrix_size", 0), ("e", [[0, 0, 1, 1]]),
                           ("e", [[1, 0, 0, 1]]), ("e", [[0, 0, 0, 0.5]])):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                certify({**base, key: value})
        with self.assertRaises(ValueError):
            FiniteGroup([[0, 1], [1, 1]])
        with self.assertRaises(ValueError):
            FiniteGroup([[0, 1], [1]])
        # A loop with identity and two-sided inverses, but not associativity.
        table = cyclic_table(6)
        table[1][1] = 3
        with self.assertRaisesRegex(ValueError, "associativity"):
            FiniteGroup(table)

    def test_certificate_cli_rejects_tampering(self):
        script = Path(__file__).with_name("kaplansky_trace_certificate.py")
        certificate = bundle(example_specs()[:2])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certificate.json"
            path.write_text(json.dumps(certificate))
            good = subprocess.run([sys.executable, str(script), "--verify", str(path)],
                                  capture_output=True, text=True)
            self.assertEqual(good.returncode, 0, good.stderr)
            tampered = deepcopy(certificate)
            tampered["cases"][1]["e"]["trace"] = 0
            path.write_text(json.dumps(tampered))
            bad = subprocess.run([sys.executable, str(script), "--verify", str(path)],
                                 capture_output=True, text=True)
            self.assertNotEqual(bad.returncode, 0)
            self.assertIn("differs from exact replay", bad.stderr)


if __name__ == "__main__":
    unittest.main()
