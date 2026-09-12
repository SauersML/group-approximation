"""Search short packet words transporting the two trace-quarter carriers.

The capacity calculation and the branch-transfer calculation produce distinct
trace-quarter projections.  This bounded exact search tests whether their
separation is repaired by an obvious short symmetry of the raw/comb packet.
All coefficients and Leavitt-prefix normal forms are exact.
"""

from fractions import Fraction
import json
from pathlib import Path
import sys

sys.path.insert(0, "experiments")

from atlas_double_pauli_comb_blocks import (  # noqa: E402
    conjugate,
    cut,
    ga_add,
    ga_equal,
    ga_mul,
    ga_single,
    ga_trace,
    rational_string,
)
from atlas_raw_branch_pauli_cell import root  # noqa: E402
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
    s,
    t,
)
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    leavitt_star,
)
from atlas_transported_coefficient_raw_character_mixing import (  # noqa: E402
    build_packet,
)


MAX_DEPTH = 2


def group_key(value):
    """Canonical key for an already reduced Leavitt-prefix group element."""
    return tuple(sorted(
        (term, coefficient)
        for term, coefficient in value.items()
        if coefficient
    ))


def build_carriers():
    comb, coefficient_involutions, cuts = build_packet()
    identity = ga_single(product())
    q = ga_add(*cuts.values())
    transported = tuple(
        conjugate(comb, involution) for involution in coefficient_involutions
    )
    corners = tuple(ga_mul(value, q, value) for value in transported)
    common = ga_mul(corners[0], corners[1])

    raw, _ = raw_and_comb()
    z001 = ga_single(root(cylinder_projection("001")))
    c11 = ga_single(product(
        raw,
        root(cylinder_projection("11")),
        raw,
        root(cylinder_projection("11")),
    ))
    pauli_carrier = ga_mul(
        cut(identity, c11, negative=True),
        cut(identity, z001, negative=True),
    )
    return raw, comb, common, conjugate(comb, pauli_carrier)


def main():
    raw, comb, common, transported_pauli_carrier = build_carriers()
    generators = (
        ("raw", raw),
        ("comb", comb),
        ("raw*", leavitt_star(raw)),
        ("comb*", leavitt_star(comb)),
        ("x0", root(t(0), 0, 1)),
        ("x1", root(t(1), 0, 1)),
        ("z0", root(s(0), 1, 2)),
        ("z1", root(s(1), 1, 2)),
    )

    identity = product()
    seen = {group_key(identity)}
    frontier = [((), identity)]
    best_overlap = Fraction(-1)
    best_words = []
    exact_words = []
    count_by_depth = [1]

    for depth in range(MAX_DEPTH + 1):
        next_frontier = []
        for word, value in frontier:
            moved = conjugate(value, transported_pauli_carrier)
            overlap = ga_trace(ga_mul(common, moved))
            if overlap > best_overlap:
                best_overlap = overlap
                best_words = [word]
            elif overlap == best_overlap:
                best_words.append(word)
            if overlap == Fraction(1, 4) and ga_equal(common, moved):
                exact_words.append(word)

            if depth == MAX_DEPTH:
                continue
            for name, generator in generators:
                child = product(value, generator)
                key = group_key(child)
                if key in seen:
                    continue
                seen.add(key)
                next_frontier.append((word + (name,), child))
        if depth < MAX_DEPTH:
            frontier = next_frontier
            count_by_depth.append(len(frontier))

    result = {
        "maximum_word_depth": MAX_DEPTH,
        "generator_names": [name for name, _ in generators],
        "distinct_reduced_expression_keys_by_minimum_depth": count_by_depth,
        "total_distinct_reduced_expression_keys": len(seen),
        "exact_conjugator_count": len(exact_words),
        "exact_conjugators": [" ".join(word) or "1" for word in exact_words],
        "maximum_overlap": rational_string(best_overlap),
        "maximum_possible_overlap_for_equality": "1/4",
        "best_words": [" ".join(word) or "1" for word in best_words],
    }
    expected_path = Path(__file__).with_name(
        "atlas-quarter-carrier-short-conjugacy.json"
    )
    with expected_path.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
