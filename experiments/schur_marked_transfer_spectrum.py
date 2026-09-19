#!/usr/bin/env python3
"""Exact marked central-character transfer spectrum for the Schur packet.

The support packet uses the central basis (J, z_e, z_f).  We exhaust
GL(3,2), retain the involutions which fix J and admit a packet-pivot chart,
and average their contragredient actions on the four characters with J=-1.

No floating-point or third-party package is used.  The asserted identity

    T = P_const + (1/5) (I - P_const)

is checked entry by entry over Fraction, so the script is a replayable exact
certificate for the transverse spectral radius 1/5.  This is only the marked
central-character sector; it does not certify contraction of the full
induction/restriction type operator.
"""
from __future__ import annotations

import json
from fractions import Fraction
from itertools import product

from schur_packet_hnn_flow_search import (
    FORBIDDEN,
    IDENTITY,
    all_gl3,
    dot3,
    mat_mul,
    mat_vec,
    packet_pivots,
    transport_character,
)


def compute() -> dict[str, object]:
    marked = tuple(c for c in product((0, 1), repeat=3) if c[0] == 1)
    index = {c: i for i, c in enumerate(marked)}
    pivots = packet_pivots()
    central_j = (1, 0, 0)

    charts = []
    for matrix in all_gl3():
        if mat_mul(matrix, matrix) != IDENTITY:
            continue
        if mat_vec(matrix, central_j) != central_j:
            continue
        if not any(
            mat_vec(matrix, source_word) in pivots
            and dot3(FORBIDDEN, source_word) == 1
            for source_word in pivots
        ):
            continue
        transported = tuple(transport_character(matrix, c) for c in marked)
        assert all(c in index for c in transported)
        charts.append((matrix, transported))

    assert len(charts) == 10
    transfer = [[Fraction(0) for _ in marked] for _ in marked]
    for _, transported in charts:
        for source, target in zip(marked, transported):
            transfer[index[target]][index[source]] += Fraction(1, len(charts))

    expected = [
        [Fraction(2, 5) if i == j else Fraction(1, 5) for j in range(4)]
        for i in range(4)
    ]
    assert transfer == expected
    assert all(sum(row) == 1 for row in transfer)
    assert all(sum(transfer[i][j] for i in range(4)) == 1 for j in range(4))

    # On constants the eigenvalue is 1.  On every zero-sum vector v,
    # (Tv)_i=(2/5)v_i+(1/5)sum_{j!=i}v_j=(1/5)v_i.
    return {
        "central_basis": ["J", "z_e", "z_f"],
        "marked_character_order": ["".join(map(str, c)) for c in marked],
        "eligible_mark_preserving_involutive_charts": len(charts),
        "transfer_matrix": [
            [str(entry) for entry in row] for row in transfer
        ],
        "constant_eigenvalue": "1",
        "transverse_eigenvalue": "1/5",
        "transverse_multiplicity": 3,
        "full_type_operator_certified": False,
    }


if __name__ == "__main__":
    print(json.dumps(compute(), indent=2, sort_keys=True))
