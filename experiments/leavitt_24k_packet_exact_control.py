"""Verify one explicit exact degree-24 model of the four-word Leavitt packet.

Run only on MSI after review. There is no search, optimization, random seed,
or checkpoint input. Permutations are image tuples, (p q)[i]=p[q[i]], matching
column matrices |i> -> |p[i]>. The certificate models only this finite packet:
the further native relation d^2=1 fails on all 24 points.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import time


DIMENSION = 24
IDENTITY = tuple(range(DIMENSION))
ROW_NAMES = ("r_star", "R_v", "R_0", "R_sum")
WORD_LENGTH_BOUNDS = (166, 16, 172, 108)
EXPECTED_SWAPS = ((9, 17), (10, 18), (12, 20), (15, 23))


def product(left, right):
    return tuple(left[right[i]] for i in range(DIMENSION))


def inverse(value):
    result = [0] * DIMENSION
    for source, target in enumerate(value):
        result[target] = source
    return tuple(result)


def commutator(left, right):
    return product(product(product(left, right), inverse(left)), inverse(right))


def conjugate(actor, value):
    return product(product(actor, value), inverse(actor))


def moved_count(value):
    return sum(source != target for source, target in enumerate(value))


def explicit_factors():
    """Indices are 8*a+x, for a in C3 and x in C2^3."""
    cycle = tuple(8 * ((a + 1) % 3) + x for a in range(3) for x in range(8))
    flips = tuple(tuple(i ^ (1 << bit) for i in range(DIMENSION))
                  for bit in range(3))
    unitary = tuple(
        8 * ((-a if bin(x).count("1") % 2 else a) % 3) + x
        for a in range(3) for x in range(8)
    )
    b = tuple(conjugate(unitary, flip) for flip in flips)
    return cycle, flips, unitary, b


def shared_packet(cycle, b):
    """Authenticated straight-line evaluator, without expanded word loops."""
    b1, b2, b3 = b

    def gamma(word):
        return conjugate(cycle, word)

    def gamma_squared(word):
        return conjugate(inverse(cycle), word)

    d = commutator(b2, gamma(b1))
    h = gamma_squared(d)
    a = commutator(d, h)
    e = gamma(d)
    j = conjugate(a, e)
    u = commutator(b2, gamma(b3))
    w = commutator(gamma_squared(b1), a)
    rows = (
        product(product(product(j, cycle), j), cycle),
        product(commutator(b3, gamma(b3)), inverse(d)),
        commutator(u, w),
        product(product(commutator(commutator(b1, gamma(b2)), h),
                        commutator(commutator(b3, gamma(b1)), gamma_squared(u))),
                inverse(a)),
    )
    return rows, {"d": d, "h": h, "a": a, "e": e, "j": j, "u": u, "w": w}


def expanded_words():
    """Independent symbolic construction; negative tokens denote inverses."""
    c, b1, b2, b3 = (1,), (2,), (3,), (4,)

    def inv(word):
        return tuple(-letter for letter in reversed(word))

    def bracket(left, right):
        return left + right + inv(left) + inv(right)

    def gamma(word):
        return c + word + inv(c)

    def gamma_squared(word):
        return inv(c) + word + c

    d = bracket(b2, gamma(b1))
    h = gamma_squared(d)
    a = bracket(d, h)
    e = gamma(d)
    j = a + e + inv(a)
    u = bracket(b2, gamma(b3))
    w = bracket(gamma_squared(b1), a)
    rows = (
        j + c + j + c,
        bracket(b3, gamma(b3)) + inv(d),
        bracket(u, w),
        bracket(bracket(b1, gamma(b2)), h)
        + bracket(bracket(b3, gamma(b1)), gamma_squared(u)) + inv(a),
    )
    return rows, d + d


def direct_word_replay(word, generators):
    """Apply the literal word right-to-left at every point, without products."""
    images = []
    for source in range(DIMENSION):
        image = source
        for token in reversed(word):
            image = generators[token][image]
        images.append(image)
    return tuple(images)


def verify():
    cycle, flips, unitary, b = explicit_factors()
    cycle_squared = product(cycle, cycle)
    rows, intermediate = shared_packet(cycle, b)
    words, omitted_word = expanded_words()
    generators = {1: cycle, 2: b[0], 3: b[1], 4: b[2]}
    generators.update({-key: inverse(value) for key, value in tuple(generators.items())})
    direct_rows = tuple(direct_word_replay(word, generators) for word in words)
    direct_omitted = direct_word_replay(omitted_word, generators)

    subgroup_words = []
    for mask in range(1, 8):
        value = IDENTITY
        for bit in range(3):
            if mask & (1 << bit):
                value = product(value, b[bit])
        subgroup_words.append(value)
    swaps = tuple((source, target) for source, target in enumerate(unitary)
                  if source < target)
    expected_b = tuple(
        tuple(8 * ((-a) % 3) + (x ^ (1 << bit))
              for a in range(3) for x in range(8))
        for bit in range(3)
    )
    checks = {
        "U_is_permutation": tuple(sorted(unitary)) == IDENTITY,
        "U_squared_identity": product(unitary, unitary) == IDENTITY,
        "U_is_exactly_the_four_stated_swaps": swaps == EXPECTED_SWAPS,
        "C_cubed_identity": product(cycle_squared, cycle) == IDENTITY,
        "C_factor_is_regular_with_multiplicity_eight": moved_count(cycle)
            == moved_count(cycle_squared) == DIMENSION,
        "D_involutions": all(product(value, value) == IDENTITY for value in flips),
        "D_pairwise_commuting": all(product(flips[i], flips[j])
                                    == product(flips[j], flips[i])
                                    for i in range(3) for j in range(i + 1, 3)),
        "B_has_the_stated_coordinate_formula": b == expected_b,
        "B_involutions": all(product(value, value) == IDENTITY for value in b),
        "B_pairwise_commuting": all(product(b[i], b[j]) == product(b[j], b[i])
                                    for i in range(3) for j in range(i + 1, 3)),
        "B_factor_is_regular_with_multiplicity_three": all(
            moved_count(value) == DIMENSION for value in subgroup_words
        ) and len(set(subgroup_words)) == 7,
        "all_nine_cross_commutators_are_C_squared": all(
            commutator(left, conjugate(cycle, right)) == cycle_squared
            for left in b for right in b
        ),
        "shared_intermediates_match_analytic_values": all(
            intermediate[name] == cycle_squared for name in ("d", "h", "e", "j", "u")
        ) and all(intermediate[name] == IDENTITY for name in ("a", "w")),
        "expanded_word_lengths_match": tuple(map(len, words)) == WORD_LENGTH_BOUNDS,
        "direct_replay_equals_shared_evaluator": direct_rows == rows,
        "all_four_packet_words_are_identity": all(row == IDENTITY for row in direct_rows),
        "omitted_d_squared_is_C": direct_omitted == cycle
            and product(intermediate["d"], intermediate["d"]) == cycle,
        "omitted_word_moves_every_point": moved_count(direct_omitted) == DIMENSION,
    }
    return {
        "checks": checks,
        "checks_passed": all(checks.values()),
        "U": unitary,
        "U_swaps_zero_based": swaps,
        "packet_word_lengths": dict(zip(ROW_NAMES, map(len, words))),
        "packet_moved_counts": dict(zip(ROW_NAMES, map(moved_count, direct_rows))),
        "omitted_native_relation": {
            "word": "d^2",
            "length": len(omitted_word),
            "permutation": direct_omitted,
            "moved_count": moved_count(direct_omitted),
            "squared_normalized_HS_defect": 2 * moved_count(direct_omitted) / DIMENSION,
            "normalized_HS_defect": math.sqrt(2 * moved_count(direct_omitted) / DIMENSION),
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New JSON path; existing output is rejected")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error("output must be new; this verifier does not overwrite files")
    started = time.monotonic()
    result = verify()
    report = {
        "schema": "leavitt-24k-packet-exact-control-v1",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "dimension": DIMENSION,
        "k": 1,
        "permutation_convention": "image tuples; (p q)[i]=p[q[i]]; matrices act on columns",
        "coordinate_convention": "index=8*a+x, a in C3, x in C2^3",
        "C_formula": "C(a,x)=(a+1,x)",
        "D_formula": "D_i(a,x)=(a,x+e_i)",
        "U_formula": "U(a,x)=((-1)^parity(x)*a,x)",
        "B_formula": "B_i(a,x)=(-a,x+e_i)",
        "search_performed": False,
        **result,
        "conclusion": (
            "The exact degree-24 model makes all four packet relations identity "
            "with the finite factors regular, so this finite packet has no positive "
            "24k feasibility gap. It is not a model of the full Leavitt group: "
            "the native relation d^2=1 has squared normalized-HS defect exactly 2."
            if result["checks_passed"] else
            "Verification failed; no model or gap conclusion is certified."
        ),
        "verification_seconds": time.monotonic() - started,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as handle:
        json.dump(report, handle, indent=2, allow_nan=False)
        handle.write("\n")
    print(json.dumps({"output": str(output), "checks_passed": result["checks_passed"],
                      "packet_moved_counts": result["packet_moved_counts"],
                      "omitted_d_squared_moved_count": result["omitted_native_relation"]["moved_count"],
                      "verification_seconds": report["verification_seconds"]}, allow_nan=False))
    return 0 if result["checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
