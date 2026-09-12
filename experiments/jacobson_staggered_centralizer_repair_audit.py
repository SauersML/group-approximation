#!/usr/bin/env python3
"""Exhaust the 1008 first-staggered-block K_P-central boundary repairs.

Run on MSI only. All arithmetic is exact over F_2. This is a bounded
linear-model audit, not a general non-MF theorem.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import os
from pathlib import Path
import resource
import time


def linear(columns: tuple[int, ...], vector: int) -> int:
    result = 0
    while vector:
        bit = vector & -vector
        result ^= columns[bit.bit_length() - 1]
        vector ^= bit
    return result


def general_linear(dimension: int) -> list[tuple[int, ...]]:
    return [columns for columns in itertools.product(range(1, 1 << dimension),
                                                     repeat=dimension)
            if len({linear(columns, v) for v in range(1 << dimension)})
            == 1 << dimension]


def inverse(columns: tuple[int, ...]) -> tuple[int, ...]:
    images = {linear(columns, v): v for v in range(1 << len(columns))}
    return tuple(images[1 << i] for i in range(len(columns)))


def basis(label: int, level: int) -> int:
    return 1 << (7 * level + label - 1)


def apply_basis_map(function, vector: int) -> int:
    result = 0
    while vector:
        bit = vector & -vector
        index = bit.bit_length() - 1
        result ^= function(index % 7 + 1, index // 7)
        vector ^= bit
    return result


def root(row: int, column: int) -> tuple[int, int, int]:
    columns = [1, 2, 4]
    columns[column - 1] ^= 1 << (row - 1)
    return tuple(columns)


def swap(first: int, second: int) -> tuple[int, int, int]:
    columns = [1, 2, 4]
    columns[first - 1], columns[second - 1] = columns[second - 1], columns[first - 1]
    return tuple(columns)


def packet(columns: tuple[int, ...], head: bool, tail: bool):
    def image(label: int, level: int) -> int:
        if level > 0 and tail:
            return basis(linear(columns, label), level)
        if level == 0 and head and label in (1, 2, 4):
            target = linear(columns, label)
            return sum(basis(e, 0) for e in (1, 2, 4) if target & e)
        return basis(label, level)
    return lambda vector: apply_basis_map(image, vector)


def old_h_basis(label: int, level: int) -> int:
    if label == 2:
        return basis(1, level + 1)
    if label == 1 and level > 0:
        return basis(2, level - 1)
    if level > 0 and label in (5, 6):
        return basis(11 - label, level)
    return basis(label, level)


def old_h(vector: int) -> int:
    return apply_basis_map(old_h_basis, vector)


# The shifted seven-point block is indexed by the original nonzero labels,
# with label 2 represented by head2 rather than the positive-level A2.
STAGGERED = tuple(basis(x, 0 if x == 2 else 1) for x in range(1, 8))
STAGGERED_MASK = sum(STAGGERED)


def block_operator(columns: tuple[int, ...]):
    global_columns = tuple(sum(STAGGERED[j] for j in range(7) if c & (1 << j))
                           for c in columns)
    def apply(vector: int) -> int:
        coordinates = sum(1 << j for j in range(7) if vector & STAGGERED[j])
        return (vector & ~STAGGERED_MASK) ^ linear(global_columns, coordinates)
    return apply


# t0,t1,t2,v0,w0,v1,w1, in the shifted standard basis.
CHANGE = (2, 1 | 8 | 16, 4 | 32 | 64, 1 | 16,
          4 | 64, 8 | 16, 32 | 64)


def centralizer_columns(trivial: tuple[int, ...], natural: tuple[int, ...],
                        change_inverse: tuple[int, ...]) -> tuple[int, ...]:
    coordinates = tuple(trivial) + tuple(c << 3 for c in natural) \
        + tuple(c << 5 for c in natural)
    return tuple(linear(CHANGE, linear(coordinates, linear(change_inverse, 1 << i)))
                 for i in range(7))


def commutator(left: tuple[str, ...], right: tuple[str, ...]) -> tuple[str, ...]:
    # Every named primitive below is an involution.
    return left + right + tuple(reversed(left)) + tuple(reversed(right))


A = ("h", "c", "h")
U_WORD = commutator(A, ("k",))
W = commutator(U_WORD, ("h", "z", "h")) + ("z",)
FIRST = ("h", "b") * 3


def evaluate(word: tuple[str, ...], vector: int, operators: dict) -> int:
    for name in reversed(word):
        vector = operators[name](vector)
    return vector


def main() -> None:
    if os.uname().sysname != "Linux":
        raise RuntimeError("Run this bounded audit on MSI only")
    resource.setrlimit(resource.RLIMIT_CPU, (18, 18))
    start = time.monotonic()
    gl3, gl2 = general_linear(3), general_linear(2)
    assert len(gl3) == 168 and len(gl2) == 6
    change_inverse = inverse(CHANGE)
    operators = {
        "c": packet(root(1, 3), False, True),
        "k": packet(root(3, 1), True, True),
        "kp": packet(root(3, 1), False, True),
        "z": packet(root(2, 3), True, True),
        "b": packet(swap(2, 3), True, True),
    }
    counts = {"candidates": 0, "W_fixes_head3": 0,
              "W_fixes_head3_and_first_braid_fixes_head": 0}
    invariant_vector_histogram = {}
    head3_survivors = []
    for trivial in gl3:
        for natural in gl2:
            columns = centralizer_columns(trivial, natural, change_inverse)
            inverse_columns = inverse(columns)
            repair, undo = block_operator(columns), block_operator(inverse_columns)
            for vector in STAGGERED:
                assert repair(undo(vector)) == vector
                assert repair(operators["c"](vector)) == operators["c"](repair(vector))
                assert repair(operators["kp"](vector)) == operators["kp"](repair(vector))
            operators["h"] = lambda vector, repair=repair, undo=undo: repair(old_h(undo(vector)))
            counts["candidates"] += 1
            inverse_head2 = linear(inverse_columns, 2)
            key = str(inverse_head2)
            bucket = invariant_vector_histogram.setdefault(key, {"count": 0,
                                                                 "W_fixes_head3": 0})
            bucket["count"] += 1
            if evaluate(W, basis(4, 0), operators) != basis(4, 0):
                continue
            counts["W_fixes_head3"] += 1
            bucket["W_fixes_head3"] += 1
            data = {"trivial_columns": trivial, "natural_columns": natural,
                    "standard_columns": columns}
            transported_head2 = operators["h"](basis(2, 0))
            first_failure = next((label for label in (1, 2, 4)
                                  if evaluate(FIRST, basis(label, 0), operators)
                                  != basis(label, 0)), None)
            # H fixes head1 and head3; therefore the first braid on the head
            # holds exactly when b fixes H(head2). Record this smaller witness.
            assert (first_failure is None) == (operators["b"](transported_head2)
                                               == transported_head2)
            head3_survivors.append(data | {
                "H_head2_bits": hex(transported_head2),
                "b_H_head2_bits": hex(operators["b"](transported_head2)),
                "first_braid_failing_head_label": first_failure,
            })
            if first_failure is not None:
                continue
            counts["W_fixes_head3_and_first_braid_fixes_head"] += 1
    assert counts == {"candidates": 1008, "W_fixes_head3": 16,
                      "W_fixes_head3_and_first_braid_fixes_head": 0}
    print(json.dumps({
        "audit": "first staggered K_P-central finite-rank repairs of A7",
        "counts": counts,
        "inverse_head2_histogram": invariant_vector_histogram,
        "W_head3_survivors": head3_survivors,
        "execution": {"location": "MSI", "cpu_limit": 1,
                      "cpu_seconds_cap": 18, "wall_seconds": time.monotonic() - start},
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "1008 specified F2 linear boundary changes; no unrestricted conclusion",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
