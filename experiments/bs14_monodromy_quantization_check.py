#!/usr/bin/env python3
"""Check root-of-unity monodromy quantization and the full-commutant gap."""

from __future__ import annotations

import cmath
import math
import random
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Trial:
    orbit_length: int
    multiplicity: int
    phase_order: int
    relation_error: float
    hs_error_sq: float
    hs_bound_sq: float
    adjoint_period_error: float
    spectral_gap: float
    spectral_gap_bound: float


def nearest_root(value: complex, order: int) -> complex:
    angle = math.atan2(value.imag, value.real)
    q = int(math.floor(order * angle / (2.0 * math.pi) + 0.5))
    return cmath.exp(2j * math.pi * q / order)


def scalar_packet(angles: np.ndarray, return_phase: complex) -> tuple[np.ndarray, np.ndarray]:
    m = len(angles)
    s = np.diag(np.exp(2j * np.pi * angles))
    r = np.zeros((m, m), dtype=np.complex128)
    for j in range(1, m):
        r[j - 1, j] = 1.0
    r[m - 1, 0] = return_phase
    return r, s


def orbit_angles(m: int, numerator: int) -> np.ndarray:
    denominator = 4**m - 1
    return np.array(
        [(pow(4, j, denominator) * numerator % denominator) / denominator for j in range(m)],
        dtype=float,
    )


def block_diag(blocks: list[np.ndarray]) -> np.ndarray:
    size = sum(block.shape[0] for block in blocks)
    out = np.zeros((size, size), dtype=np.complex128)
    start = 0
    for block in blocks:
        stop = start + block.shape[0]
        out[start:stop, start:stop] = block
        start = stop
    return out


def normalized_frobenius_sq(a: np.ndarray) -> float:
    return float(np.linalg.norm(a, "fro") ** 2 / a.shape[0])


def commutant_adjoint_matrix(r: np.ndarray, m: int, multiplicity: int) -> np.ndarray:
    """Matrix of Ad(r) on span{|j,a><j,b|}, packet-major coordinates."""
    basis: list[np.ndarray] = []
    d = m * multiplicity
    for j in range(m):
        for a in range(multiplicity):
            for b in range(multiplicity):
                e = np.zeros((d, d), dtype=np.complex128)
                row = a * m + j
                col = b * m + j
                e[row, col] = 1.0
                basis.append(e)

    q = len(basis)
    psi = np.zeros((q, q), dtype=np.complex128)
    r_star = r.conj().T
    # The basis is orthonormal for the unnormalized Frobenius product.
    for column, e in enumerate(basis):
        image = r @ e @ r_star
        for row, f in enumerate(basis):
            psi[row, column] = np.vdot(f, image)
    return psi


def run_trial(rng: random.Random, m: int, multiplicity: int, phase_order: int) -> Trial:
    denominator = 4**m - 1
    # Reject numerators whose orbit has smaller period, so the tested commutant
    # block has the advertised minimal orbit length.
    while True:
        numerator = rng.randrange(1, denominator)
        residues = [pow(4, j, denominator) * numerator % denominator for j in range(m)]
        if len(set(residues)) == m:
            break
    angles = orbit_angles(m, numerator)

    original_phases = [cmath.exp(2j * math.pi * rng.random()) for _ in range(multiplicity)]
    rounded_phases = [nearest_root(v, phase_order) for v in original_phases]

    r_blocks: list[np.ndarray] = []
    rq_blocks: list[np.ndarray] = []
    s_blocks: list[np.ndarray] = []
    for v, w in zip(original_phases, rounded_phases):
        r, s = scalar_packet(angles, v)
        rq, _ = scalar_packet(angles, w)
        r_blocks.append(r)
        rq_blocks.append(rq)
        s_blocks.append(s)

    r = block_diag(r_blocks)
    rq = block_diag(rq_blocks)
    s = block_diag(s_blocks)
    d = r.shape[0]

    relation = rq @ s @ rq.conj().T - np.linalg.matrix_power(s, 4)
    relation_error = float(np.linalg.norm(relation, "fro") / math.sqrt(d))
    hs_error_sq = normalized_frobenius_sq(r - rq)
    hs_bound_sq = math.pi**2 / phase_order**2

    psi = commutant_adjoint_matrix(rq, m, multiplicity)
    period = m * phase_order
    adjoint_period_error = float(
        np.linalg.norm(np.linalg.matrix_power(psi, period) - np.eye(psi.shape[0]), "fro")
        / math.sqrt(psi.shape[0])
    )
    eigenvalues = np.linalg.eigvals(psi)
    distances = [abs(1.0 - z) for z in eigenvalues if abs(1.0 - z) > 1e-7]
    spectral_gap = min(distances) if distances else math.inf
    spectral_gap_bound = 2.0 * math.sin(math.pi / period)

    tolerance = 2e-8
    assert relation_error <= tolerance, relation_error
    assert hs_error_sq <= hs_bound_sq + tolerance, (hs_error_sq, hs_bound_sq)
    assert adjoint_period_error <= tolerance, adjoint_period_error
    assert spectral_gap + tolerance >= spectral_gap_bound, (spectral_gap, spectral_gap_bound)

    return Trial(
        m,
        multiplicity,
        phase_order,
        relation_error,
        hs_error_sq,
        hs_bound_sq,
        adjoint_period_error,
        spectral_gap,
        spectral_gap_bound,
    )


def main() -> None:
    rng = random.Random(20260822)
    trials: list[Trial] = []
    for m in range(1, 8):
        for multiplicity in range(1, 5):
            for phase_order in range(2, 10):
                for _ in range(2):
                    trials.append(run_trial(rng, m, multiplicity, phase_order))

    max_relation = max(t.relation_error for t in trials)
    max_hs_ratio = max(t.hs_error_sq / t.hs_bound_sq for t in trials)
    max_period_error = max(t.adjoint_period_error for t in trials)
    min_gap_ratio = min(
        t.spectral_gap / t.spectral_gap_bound
        for t in trials
        if math.isfinite(t.spectral_gap)
    )
    print(f"verified {len(trials)} monodromy-quantized packet blocks")
    print(f"max relation error: {max_relation:.3e}")
    print(f"max HS-bound ratio: {max_hs_ratio:.6f}")
    print(f"max adjoint-period error: {max_period_error:.3e}")
    print(f"min spectral-gap ratio: {min_gap_ratio:.6f}")


if __name__ == "__main__":
    main()
