#!/usr/bin/env python3
"""Numerical sanity check for bounded-cycle shadowing of exact BS(1,4) packets."""

from __future__ import annotations

import math
import random
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Trial:
    m: int
    k_cap: int
    r_error_sq: float
    s_error_sq: float
    r_bound_sq: float
    s_bound_sq: float
    relation_error: float


def partition_sizes(m: int, k_cap: int) -> list[int]:
    if m <= k_cap:
        return [m]
    block_count = math.ceil(m / k_cap)
    small, remainder = divmod(m, block_count)
    sizes = [small + 1] * remainder + [small] * (block_count - remainder)
    assert sum(sizes) == m
    assert max(sizes) <= k_cap
    return sizes


def scalar_packet(m: int, numerator: int, phase: complex) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    denominator = 4**m - 1
    theta = numerator / denominator
    angles = np.array([(pow(4, j, denominator) * numerator % denominator) / denominator for j in range(m)])
    s = np.diag(np.exp(2j * np.pi * angles))
    r = np.zeros((m, m), dtype=np.complex128)
    for j in range(1, m):
        r[j - 1, j] = 1.0
    r[m - 1, 0] = phase
    return r, s, angles


def truncate_packet(r: np.ndarray, angles: np.ndarray, k_cap: int, phase: complex) -> tuple[np.ndarray, np.ndarray]:
    m = len(angles)
    if m <= k_cap:
        return r.copy(), np.diag(np.exp(2j * np.pi * angles))

    r_new = np.zeros_like(r)
    new_angles = np.zeros(m)
    start = 0
    for block_index, length in enumerate(partition_sizes(m, k_cap)):
        stop = start + length
        alpha = float(angles[start])
        denominator = 4**length - 1
        q = int(math.floor(denominator * alpha + 0.5))
        eta = (q / denominator) % 1.0
        for offset in range(length):
            new_angles[start + offset] = (pow(4, offset, denominator) * q % denominator) / denominator
        for j in range(start + 1, stop):
            r_new[j - 1, j] = 1.0
        closing_phase = phase if block_index == 0 else 1.0
        r_new[stop - 1, start] = closing_phase
        start = stop

    return r_new, np.diag(np.exp(2j * np.pi * new_angles))


def normalized_frobenius_sq(a: np.ndarray) -> float:
    return float(np.linalg.norm(a, "fro") ** 2 / a.shape[0])


def run_trial(rng: random.Random, m: int, k_cap: int) -> Trial:
    denominator = 4**m - 1
    numerator = rng.randrange(1, denominator)
    phase = np.exp(2j * np.pi * rng.random())
    r, s, angles = scalar_packet(m, numerator, phase)
    r_new, s_new = truncate_packet(r, angles, k_cap, phase)

    relation = r_new @ s_new @ r_new.conj().T - np.linalg.matrix_power(s_new, 4)
    relation_error = float(np.linalg.norm(relation, "fro") / math.sqrt(m))
    r_error_sq = normalized_frobenius_sq(r - r_new)
    s_error_sq = normalized_frobenius_sq(s - s_new)
    r_bound_sq = 8.0 / k_cap
    s_bound_sq = 2.0 * math.pi**2 / (9.0 * k_cap)

    tolerance = 2e-9
    assert relation_error <= tolerance, relation_error
    assert r_error_sq <= r_bound_sq + tolerance, (r_error_sq, r_bound_sq)
    assert s_error_sq <= s_bound_sq + tolerance, (s_error_sq, s_bound_sq)
    return Trial(m, k_cap, r_error_sq, s_error_sq, r_bound_sq, s_bound_sq, relation_error)


def main() -> None:
    rng = random.Random(20260822)
    trials: list[Trial] = []
    for k_cap in range(2, 13):
        for m in range(2, 31):
            for _ in range(4):
                trials.append(run_trial(rng, m, k_cap))

    max_relation = max(t.relation_error for t in trials)
    max_r_ratio = max(t.r_error_sq / t.r_bound_sq for t in trials)
    max_s_ratio = max(t.s_error_sq / t.s_bound_sq for t in trials)
    print(f"verified {len(trials)} exact packet truncations")
    print(f"max relation error: {max_relation:.3e}")
    print(f"max R-bound ratio: {max_r_ratio:.6f}")
    print(f"max S-bound ratio: {max_s_ratio:.6f}")


if __name__ == "__main__":
    main()
