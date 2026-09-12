#!/usr/bin/env python3
"""Exact F2 audit of the five-selector full-character reset count.

This is deliberately tiny: it checks the symplectic ranks and commutators
which distinguish the corrected twenty-qubit packet from the invalid
nineteen-qubit coarse reset-sign count.
"""

import json


N = 5  # four semantic selector qubits and one dummy qubit


def dot(a, b):
    return bin(a & b).count("1") & 1


def omega(v, w):
    x, z = v
    y, t = w
    return dot(x, t) ^ dot(z, y)


def rank_f2(rows):
    rows = rows[:]
    rank = 0
    for col in range(2 * N - 1, -1, -1):
        pivot = next((j for j in range(rank, len(rows)) if (rows[j] >> col) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for j in range(len(rows)):
            if j != rank and ((rows[j] >> col) & 1):
                rows[j] ^= rows[rank]
        rank += 1
    return rank


def pack(v):
    return v[0] | (v[1] << N)


def z(mask):
    return (0, mask)


def x(mask):
    return (mask, 0)


semantic_mask = 0b01111
dummy_mask = 0b10000

# Representative nonzero reset a=(1,1,1,1).  The three ell rows form a
# basis of a^perp modulo the reset coordinate.
t_a = x(semantic_mask)
ell = [z(0b00011), z(0b00101), z(0b01001)]
fresh = [t_a, *ell]
old = [z(1 << i) for i in range(4)]
dummy_pair = [x(dummy_mask), z(dummy_mask)]

assert all(omega(v, w) == 0 for i, v in enumerate(fresh) for w in fresh[i + 1 :])
assert rank_f2([pack(v) for v in fresh]) == 4
assert rank_f2([pack(v) for v in old]) == 4
assert all(omega(v, d) == 0 for v in fresh for d in dummy_pair)
assert omega(dummy_pair[0], dummy_pair[1]) == 1

report = {
    "selector_qubits": N,
    "semantic_qubits": 4,
    "dummy_qubits": 1,
    "old_full_character_stabilizer_rank": rank_f2([pack(v) for v in old]),
    "fresh_full_character_stabilizer_rank": rank_f2([pack(v) for v in fresh]),
    "old_full_character_dimension": 2 ** (N - rank_f2([pack(v) for v in old])),
    "fresh_full_character_dimension": 2 ** (N - rank_f2([pack(v) for v in fresh])),
    "dummy_pair_commutes_with_fresh_selectors": True,
    "dummy_pair_symplectic_pairing": omega(dummy_pair[0], dummy_pair[1]),
    "residual_spin_dimension": 2**15,
    "old_rank16_carrier_dimension": 2 ** (N - 4) * 2**15,
    "fresh_rank16_carrier_dimension": 2 ** (N - 4) * 2**15,
    "nineteen_qubit_without_dummy_full_character_dimension": 1,
}

print(json.dumps(report, indent=2, sort_keys=True))
