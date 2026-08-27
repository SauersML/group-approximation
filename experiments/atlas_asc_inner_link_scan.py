"""Exact inner-conjugator test of the (LINK) inequality.

At `U = lambda(t)` everything is exact integer combinatorics, so the question

    sum_s l_s^2  <=  C' * sum_s ||pi_U(s)-1||_2^2                    (LINK)

can be decided on the 20160 inner chart conjugators without any numerics:

  * the true defect is `||lambda(w_t(s)) - 1||_2`, which is 0 when the word
    evaluates to the identity under `g -> t g t^(-1)` on the second chart and
    `sqrt(2)` otherwise;
  * the linearized defect is `l_s = ||rho(z_s) lambda(t)||_2` with
    `rho(x)lambda(t) = lambda(x t x^(-1))`, so
    `rho(z_s)lambda(t) = sum_j (lambda(u_j t u_j^(-1)) - lambda(v_j t v_j^(-1)))`
    and, distinct group elements being orthonormal in normalized HS,
    `l_s^2 = sum_g c_g^2` over the integer coefficients of that sum.

A `t` that kills every word while leaving some `l_s > 0` refutes (LINK)
globally in one line -- and would say the local half of (ASC) cannot be
closed by comparing the two energies without first localizing.
"""

import argparse
import json
import os
import sys
from collections import Counter

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_asc_packet_build import code_of, index_group, merge  # noqa: E402
from atlas_boundary_amalgam_normal_form import transported_word  # noqa: E402
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_certified_a8_alignment import boundary_words  # noqa: E402
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key  # noqa

ORDER = 20160


def prefixes(word):
    """(u_j, v_j) for every K2 syllable, plus the fold value."""
    pairs, prefix = [], I4.copy()
    for factor, matrix in word:
        image = gf2_mul(prefix, matrix)
        if factor == 2:
            pairs.append((prefix.copy(), image.copy()))
        prefix = image
    return pairs, prefix


def conjugate(x, t):
    return gf2_mul(gf2_mul(x, t), gf2_inv(x))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    rows, table, elements = index_group()

    words = [merge(transported_word(raw, alignment, alignment_inverse))
             for raw in boundary_words()]
    data = []
    for word in words:
        pairs, fold = prefixes(word)
        if not np.array_equal(fold, I4):
            raise AssertionError("a boundary word is not fold-trivial")
        data.append((word, pairs))

    killers, report = [], []
    for position, t in enumerate(elements):
        kills = True
        for word, _pairs in data:
            value = I4.copy()
            for factor, matrix in word:
                image = conjugate(t, matrix) if factor == 2 else matrix
                value = gf2_mul(value, image)
            if not np.array_equal(value, I4):
                kills = False
                break
        if not kills:
            continue
        # linearized energy at this exact solution
        total = 0
        per_word = []
        for _word, pairs in data:
            counts = Counter()
            for u, v in pairs:
                counts[matrix_key(conjugate(u, t))] += 1
                counts[matrix_key(conjugate(v, t))] -= 1
            energy = sum(value * value for value in counts.values())
            per_word.append(energy)
            total += energy
        killers.append({
            "t_hex": matrix_key(t).hex(),
            "is_identity": bool(np.array_equal(t, I4)),
            "sum_linear_energy": int(total),
            "max_word_linear_energy": int(max(per_word)),
            "words_with_nonzero_linear": int(sum(1 for e in per_word if e)),
        })
        report.append(position)

    out = {
        "inner_conjugators_scanned": ORDER,
        "words": len(words),
        "exact_solutions": len(killers),
        "solutions": killers[:20],
        "link_refuted_by_inner_conjugator": bool(
            any(entry["sum_linear_energy"] > 0 for entry in killers)),
    }
    text = json.dumps(out, indent=2, sort_keys=True)
    print(text)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as stream:
            stream.write(text + "\n")


if __name__ == "__main__":
    main()
