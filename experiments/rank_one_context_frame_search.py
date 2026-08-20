#!/usr/bin/env python3
"""Exhaust four-generator paired frames for one relative Pauli coordinate.

Let F be a rank-two alternating form on F_2^4.  A paired frame with
coefficient word matrix C has symbolic commutator map

    omega |-> (F(omega), (C F C^T)(omega)).

Two frames with the same kernel define the same class-two edge group (up to a
central basis change).  We classify, inside each kernel class, the evaluated
rank profiles at endpoint bits 00,10,01,11.  The desired local phenomenon is
two isomorphic frames whose profiles agree away from 11 and differ there by
one alternating rank, i.e. one Pauli factor.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import product

Bit4 = tuple[int, int, int, int]
Matrix4 = tuple[Bit4, Bit4, Bit4, Bit4]
PAIRS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
F: Matrix4 = (
    (0, 0, 1, 0),
    (0, 0, 0, 0),
    (1, 0, 0, 0),
    (0, 0, 0, 0),
)


def rank_f2(rows: tuple[tuple[int, ...], ...]) -> int:
    work = [list(row) for row in rows]
    rank = 0
    for column in range(len(work[0]) if work else 0):
        pivot = next(
            (row for row in range(rank, len(work)) if work[row][column]),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for row in range(len(work)):
            if row != rank and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[rank])]
        rank += 1
    return rank


def pull(matrix: Matrix4) -> Matrix4:
    return tuple(
        tuple(
            sum(
                matrix[row][left]
                & F[left][right]
                & matrix[column][right]
                for left in range(4)
                for right in range(4)
            )
            & 1
            for column in range(4)
        )
        for row in range(4)
    )  # type: ignore[return-value]


def add(left: Matrix4, right: Matrix4) -> Matrix4:
    return tuple(
        tuple(left[row][column] ^ right[row][column] for column in range(4))
        for row in range(4)
    )  # type: ignore[return-value]


def kernel_code(second: Matrix4) -> int:
    columns = tuple((F[left][right], second[left][right]) for left, right in PAIRS)
    code = 0
    for index, coefficients in enumerate(product((0, 1), repeat=6)):
        value = [0, 0]
        for bit, column in zip(coefficients, columns):
            if bit:
                value[0] ^= column[0]
                value[1] ^= column[1]
        if value == [0, 0]:
            code |= 1 << index
    return code


def weight(matrix: Matrix4) -> int:
    return sum(sum(row) for row in matrix)


def audit() -> None:
    classes: dict[int, dict[tuple[int, int, int, int], Matrix4]] = defaultdict(dict)
    for flat in product((0, 1), repeat=16):
        matrix: Matrix4 = tuple(
            tuple(flat[4 * row : 4 * row + 4]) for row in range(4)
        )  # type: ignore[assignment]
        second = pull(matrix)
        profile = (0, rank_f2(F), rank_f2(second), rank_f2(add(F, second)))
        code = kernel_code(second)
        previous = classes[code].get(profile)
        if previous is None or weight(matrix) < weight(previous):
            classes[code][profile] = matrix

    one_pauli_witnesses = []
    two_pauli_witnesses = []
    for code, profiles in classes.items():
        profile_set = set(profiles)
        for low in profile_set:
            for high in profile_set:
                jump = abs(low[3] - high[3])
                if low[:3] == high[:3] and jump in (2, 4):
                    destination = (
                        one_pauli_witnesses if jump == 2 else two_pauli_witnesses
                    )
                    destination.append(
                        (
                            weight(profiles[low]) + weight(profiles[high]),
                            code,
                            low,
                            high,
                            profiles[low],
                            profiles[high],
                        )
                    )
    one_pauli_witnesses.sort(key=lambda item: (item[0], item[2], item[3]))
    two_pauli_witnesses.sort(key=lambda item: (item[0], item[2], item[3]))

    print(f"matrices checked={1 << 16}")
    print(f"symbolic kernel classes={len(classes)}")
    print(f"one-Pauli-at-11 witness pairs={len(one_pauli_witnesses)}")
    print(f"two-Pauli-at-11 witness pairs={len(two_pauli_witnesses)}")
    profile_families = sorted(
        {tuple(sorted(profiles)) for profiles in classes.values()},
        key=lambda family: (len(family), family),
    )
    print(f"distinct within-kernel profile families={len(profile_families)}")
    for family in profile_families:
        print(f"  {family}")
    for total_weight, _, low, high, low_matrix, high_matrix in two_pauli_witnesses[:12]:
        print(
            f"weight={total_weight} profiles={low}->{high} "
            f"C_low={low_matrix} C_high={high_matrix}"
        )

    assert not one_pauli_witnesses
    assert not two_pauli_witnesses


if __name__ == "__main__":
    audit()
