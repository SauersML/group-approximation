"""Exact raw-character mixing table for the comb-transported coefficient involutions.

The four raw coefficient character cuts F_epsilon split the two-sheet corner q.
For T_i = comb^* B_i comb, compute the exact canonical-trace block masses

    tau(F_epsilon T_i F_delta T_i).

Each contraction is an exact rational binary Leavitt-prefix calculation.  The
32 independent contractions are farmed to a small process pool because the
normal-form reductions are CPU-bound; the checked JSON is the certificate.
"""

from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, "experiments")

from atlas_double_pauli_comb_blocks import (  # noqa: E402
    conjugate,
    cut,
    ga_add,
    ga_mul,
    ga_scale,
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


CHARACTERS = ((-1, -1), (-1, 1), (1, -1), (1, 1))


def build_packet():
    """Return comb, the two raw coefficient involutions, and four raw cuts."""
    raw, comb = raw_and_comb()
    identity = ga_single(product())
    x = (root(t(0), 0, 1), root(t(1), 0, 1))
    z = (root(s(0), 1, 2), root(s(1), 1, 2))
    c_raw = tuple(product(raw, value, raw, value) for value in x)
    a = tuple(product(x[index], c_raw[index]) for index in range(2))
    c = product(x[0], z[0], x[0], z[0])
    d = product(c_raw[0], z[0], c_raw[0], z[0])

    q = cut(identity, ga_single(d), negative=True)
    p = cut(identity, ga_single(c), negative=True)
    coefficient_involutions = tuple(
        ga_add(
            ga_mul(p, ga_single(a[index])),
            ga_mul(ga_sub(identity, p), ga_single(x[index])),
        )
        for index in range(2)
    )

    cuts = {}
    for epsilon0, epsilon1 in CHARACTERS:
        f0 = cut(q, coefficient_involutions[0], negative=epsilon0 == -1)
        f1 = cut(q, coefficient_involutions[1], negative=epsilon1 == -1)
        cuts[(epsilon0, epsilon1)] = ga_mul(f0, f1)
    return comb, coefficient_involutions, cuts


def block_mass(task):
    """Compute one exact entry tau(F_e T_i F_d T_i)."""
    involution_index, source_index, target_index = task
    comb, coefficient_involutions, cuts = build_packet()
    transported = conjugate(comb, coefficient_involutions[involution_index])
    source = cuts[CHARACTERS[source_index]]
    target = cuts[CHARACTERS[target_index]]
    value = ga_trace(ga_mul(source, transported, target, transported))
    return involution_index, source_index, target_index, value


def expected_closed_form(involution_index, source_index, target_index):
    diagonal = source_index == target_index
    if involution_index == 0:
        return Fraction(21 if diagonal else 1, 256)
    return Fraction(5 if diagonal else 1, 128)


def main():
    tasks = [
        (involution_index, source_index, target_index)
        for involution_index in range(2)
        for source_index in range(4)
        for target_index in range(4)
    ]
    worker_count = min(8, os.cpu_count() or 1)
    with ProcessPoolExecutor(max_workers=worker_count) as executor:
        entries = list(executor.map(block_mass, tasks))

    tables = [[[
        Fraction(0) for _ in range(4)
    ] for _ in range(4)] for _ in range(2)]
    for involution_index, source_index, target_index, value in entries:
        expected = expected_closed_form(
            involution_index, source_index, target_index)
        if value != expected:
            raise AssertionError((
                involution_index, source_index, target_index, value, expected))
        tables[involution_index][source_index][target_index] = value

    # Each raw character cut has trace 1/8.  After normalizing one row by that
    # trace, the block table is a substochastic 4-state kernel.  Its constant
    # eigenvalue is the survival mass in q; its other three eigenvalues are the
    # centered contraction factor.
    normalized = [
        [[8 * value for value in row] for row in table]
        for table in tables
    ]
    survival = [sum(table[0]) for table in normalized]
    centered = [table[0][0] - table[0][1] for table in normalized]

    result = {
        "character_order": [str(value) for value in CHARACTERS],
        "raw_character_trace": "1/8",
        "transported_B0_block_masses": [
            [rational_string(value) for value in row] for row in tables[0]
        ],
        "transported_B1_block_masses": [
            [rational_string(value) for value in row] for row in tables[1]
        ],
        "closed_forms": {
            "transported_B0": "(20 I + J) / 256",
            "transported_B1": "(4 I + J) / 128",
        },
        "raw_trace_normalized_substochastic_kernels": {
            "transported_B0": "(20 I + J) / 32",
            "transported_B1": "(4 I + J) / 16",
        },
        "survival_masses": [rational_string(value) for value in survival],
        "centered_contraction_factors": [
            rational_string(value) for value in centered
        ],
    }

    expected_path = Path(__file__).with_name(
        "atlas-transported-coefficient-raw-character-mixing.json")
    with expected_path.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
