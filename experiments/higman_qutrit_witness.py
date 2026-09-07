#!/usr/bin/env python3
"""Reconstruct the exact 3-by-3 Higman counterexample at coefficient 16.

All inputs below are integers. Optimization was used to find the parameters,
but neither optimization nor floating-point arithmetic is used in this replay.
"""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from hs_word_certificate import cayley, check, encode_matrix


ROOT = Path(__file__).resolve().parents[1]
WITNESS = ROOT / "research/artifacts/higman-qutrit-coefficient-witness.json"
NUMERATORS = (
    (-46, -56, -20, 122, -1, -67, 28, -1, 90),
    (-38, -38, 76, 42, 42, 24, -47, -12, -37),
    (-82, 33, -86, 15, 48, -115, -87, -7, 46),
    (-26, -33, 59, 0, 67, 45, -30, 32, 34),
)
DENOMINATOR = 64
CANDIDATE = {
    "generators": ["a", "b", "c", "d"],
    "relators": [[1, 2, -1, -2, -2], [2, 3, -2, -3, -3],
                 [3, 4, -3, -4, -4], [4, 1, -4, -1, -1]],
    "word": [1], "coefficient": "16",
}


def witness():
    matrices = [cayley([Q(n, DENOMINATOR) for n in row], 3) for row in NUMERATORS]
    result = check(CANDIDATE, matrices)
    if not (Q(result["word_energy"]) > Q(16, 7) and
            Q(result["relator_energy_sum"]) < Q(1, 7) and
            result["status"] == "counterexample"):
        raise ValueError("the exact rational separating bounds failed")
    return {"format": "hs-word-counterexample-v1", "candidate": CANDIDATE,
            "construction": {"type": "rational-skew-hermitian-cayley",
                             "denominator": DENOMINATOR,
                             "integer_parameters": [list(row) for row in NUMERATORS]},
            "matrices": [encode_matrix(a) for a in matrices], "verification": result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the deterministic witness")
    args = parser.parse_args()
    rendered = json.dumps(witness(), indent=2) + "\n"
    if args.write:
        WITNESS.write_text(rendered, encoding="utf-8")
    elif WITNESS.read_text(encoding="utf-8") != rendered:
        parser.exit(1, "the committed witness differs from the exact reconstruction\n")
    print("PASS: exact U(3) witness; e_a > 16/7 and total relator energy < 1/7")
    print("Coefficient 16 is false. No all-dimensions upper bound or existence proof is supplied.")


if __name__ == "__main__":
    main()
