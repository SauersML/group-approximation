"""Audit the first exceptional raw/comb mixed commutator.

The transported generator ``X1' = comb* X1 comb`` and ``raw`` are
involutions.  Their commutator ``h=X1' raw X1' raw`` is the only one among
the five first transported-generator/raw commutators whose period is not
detected through exponent 128.  This bounded exact audit records the first
sixteen powers and their action on one raw coefficient cut.
"""

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, "experiments")

from atlas_double_pauli_comb_blocks import (  # noqa: E402
    cut,
    ga_add,
    ga_equal,
    ga_mul,
    ga_single,
    ga_sub,
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
from atlas_survivor_prefix_obstruction import leavitt_star  # noqa: E402


def prefix_metrics(value):
    minimum_degree = min(
        (len(left) - len(right) for left, right in value), default=0)
    extreme_terms = [
        (left, right) for left, right in value
        if len(left) - len(right) == minimum_degree
    ]
    return {
        "terms": len(value),
        "max_left_depth": max((len(left) for left, _right in value), default=0),
        "max_right_depth": max((len(right) for _left, right in value), default=0),
        "degree_range": [
            minimum_degree,
            max((len(left) - len(right) for left, right in value), default=0),
        ],
        "minimum_degree_term_count": len(extreme_terms),
    }


def bit_word(value):
    return "".join(str(bit) for bit in value) or "1"


def main():
    raw, comb = raw_and_comb()
    identity = product()
    x = (
        root(t(0), 0, 1),
        root(t(1), 0, 1),
    )
    z = (
        root(s(0), 1, 2),
        root(s(1), 1, 2),
    )
    transported_x1 = product(leavitt_star(comb), x[1], comb)
    h = product(transported_x1, raw, transported_x1, raw)
    h_inverse = product(raw, transported_x1, raw, transported_x1)

    c_raw = tuple(product(raw, value, raw, value) for value in x)
    a = tuple(product(x[index], c_raw[index]) for index in range(2))
    c = product(x[0], z[0], x[0], z[0])
    d = product(c_raw[0], z[0], c_raw[0], z[0])
    identity_ga = ga_single(identity)
    q = cut(identity_ga, ga_single(d), negative=True)
    p = cut(identity_ga, ga_single(c), negative=True)
    b = tuple(ga_add(
        ga_mul(p, ga_single(a[index])),
        ga_mul(ga_sub(identity_ga, p), ga_single(x[index])),
    ) for index in range(2))
    f0 = cut(q, b[0], negative=True)
    f1 = cut(q, b[1], negative=True)
    source_cut = ga_mul(f0, f1)

    powers = []
    seen = []
    power = identity
    inverse_power = identity
    for exponent in range(17):
        moved = ga_mul(
            ga_single(power), source_cut, ga_single(inverse_power))
        minimum_degree = -8 * exponent
        minimum_degree_terms = [
            (left, right) for left, right in power
            if len(left) - len(right) == minimum_degree
        ]
        expected_minimum_term = (
            ((), ()) if exponent == 0 else
            ((0, 0), (0, 0) + (1, 0) * (4 * exponent))
        )
        powers.append({
            "exponent": exponent,
            **prefix_metrics(power),
            "minimum_degree_formula_holds":
                minimum_degree_terms == [expected_minimum_term],
            "source_cut_overlap_trace": rational_string(
                ga_trace(ga_mul(source_cut, moved))),
            "cut_terms": len(moved),
            "returns_to_source_cut": ga_equal(moved, source_cut),
        })
        seen.append(power)
        power = product(power, h)
        inverse_power = product(h_inverse, inverse_power)

    result = {
        "word": "h=[comb* X1 comb,raw]",
        "commutator_metrics": prefix_metrics(h),
        "commutator_minimum_degree_terms": [
            [bit_word(left), bit_word(right)]
            for left, right in h
            if len(left) - len(right) == -8
        ],
        "distinct_powers_through_16": len({
            tuple(sorted(value.items())) for value in seen
        }),
        "power_term_counts": [entry["terms"] for entry in powers],
        "power_degree_ranges": [entry["degree_range"] for entry in powers],
        "unique_minimum_degree_term_through_16": all(
            entry["minimum_degree_term_count"] == 1 for entry in powers),
        "minimum_degree_formula_through_16": all(
            entry["minimum_degree_formula_holds"] for entry in powers),
        "source_cut_overlap_trace_histogram": dict(sorted(Counter(
            entry["source_cut_overlap_trace"] for entry in powers
        ).items())),
        "source_cut_term_counts": sorted(set(
            entry["cut_terms"] for entry in powers)),
        "source_cut_return_exponents": [
            entry["exponent"] for entry in powers
            if entry["returns_to_source_cut"]
        ],
    }
    expected_path = Path(__file__).with_name(
        "atlas-mixed-commutator-dynamics.json")
    with expected_path.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
