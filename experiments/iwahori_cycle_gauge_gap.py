#!/usr/bin/env python3
"""Gauge-quotiented Iwahori row gaps on exact fourth-power packets.

The square-free presentation is

    <x,r,t | x^2, (xr)^2, (xt)^3,
               r t r^-1 t^-4, (x t^2 r)^3>.

For the exact projective action of PSL_2(F_p) on P^1(F_p), and optionally
for the compressed even-Weil outliers, this script linearizes the four rows
containing x under

    X_epsilon = exp(epsilon A) X,       A in {T}'.

The Weyl-conjugacy residual has derivative

    D A = A - Ad(R^-1)(A).

On ker(D)^perp, the inverse-Koopman energy of D A is exactly ||A||_2^2.
We therefore report the smallest singular values of the row operators on
that quotient.  The commutant basis includes every matrix multiplicity at a
T-eigenvalue.  For a heterogeneous list of primes, it also includes all
cross-summand intertwiners at shared eigenvalues (in particular the large
eigenvalue-one block), so the calculation is not restricted to scalar
Fourier gauges.

This is a finite diagnostic.  The accompanying Cairn claim proves the
dimension-free same-core lower bound algebraically; these numbers check the
word conventions and expose which smaller row sets do or do not have a gap.
"""

from __future__ import annotations

import argparse
import json
import math
from collections.abc import Callable, Sequence

import numpy as np


def normalized_frobenius(a: np.ndarray) -> float:
    return float(np.linalg.norm(a, "fro") / math.sqrt(a.shape[0]))


def projective_permutation(p: int, g: tuple[tuple[int, int], tuple[int, int]]) -> np.ndarray:
    """Permutation matrix of g on F_p union {infinity}, with z represented by (z:1)."""
    d = p + 1
    out = np.zeros((d, d), dtype=complex)
    for z in range(d):
        if z == p:
            numerator = g[0][0] % p
            denominator = g[1][0] % p
        else:
            numerator = (g[0][0] * z + g[0][1]) % p
            denominator = (g[1][0] * z + g[1][1]) % p
        image = p if denominator == 0 else (numerator * pow(denominator, -1, p)) % p
        out[image, z] = 1.0
    return out


def endpoint(p: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    inv2 = pow(2, -1, p)
    x = projective_permutation(p, ((0, -1), (1, 0)))
    r = projective_permutation(p, ((2, 0), (0, inv2)))
    t = projective_permutation(p, ((1, 1), (0, 1)))
    return x, r, t


def even_weil_compression(p: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Compressed even Weil tuple in square-free coordinates for p = 1 mod 8.

    The full Schrodinger formulas are the ones in
    even-weil-two-carrier-gauss-angle-proof.  Removing delta_0 preserves the
    exact (R,T) core; polar-sign correction of the compressed Fourier
    involution preserves X^2=(XR)^2=1 and leaves only the two cubic defects.
    """
    if p % 8 != 1:
        raise ValueError(f"the implemented phase convention requires p = 1 mod 8, got {p}")
    zeta = np.exp(2j * np.pi / p)
    inv2 = pow(2, -1, p)
    inv4 = pow(4, -1, p)

    x_full = np.empty((p, p), dtype=complex)
    for y in range(p):
        for x in range(p):
            x_full[y, x] = zeta ** ((x * y) % p) / math.sqrt(p)
    s_full = np.diag([zeta ** ((inv4 * x * x) % p) for x in range(p)])
    r_full = np.zeros((p, p), dtype=complex)
    for x in range(p):
        r_full[x, (2 * x) % p] = 1.0

    even_dimension = (p + 1) // 2
    even_basis = np.zeros((p, even_dimension), dtype=complex)
    even_basis[0, 0] = 1.0
    for column, x in enumerate(range(1, (p + 1) // 2), start=1):
        even_basis[x, column] = 1.0 / math.sqrt(2.0)
        even_basis[-x % p, column] = 1.0 / math.sqrt(2.0)

    x_even = even_basis.conj().T @ x_full @ even_basis
    r_even = even_basis.conj().T @ r_full @ even_basis
    s_even = even_basis.conj().T @ s_full @ even_basis

    compressed_x = x_even[1:, 1:]
    eigenvalues, eigenvectors = np.linalg.eigh((compressed_x + compressed_x.conj().T) / 2.0)
    signs = np.where(eigenvalues >= 0.0, 1.0, -1.0)
    x_polar = (eigenvectors * signs) @ eigenvectors.conj().T
    r = r_even[1:, 1:]
    t = np.linalg.matrix_power(s_even[1:, 1:], 2)
    return x_polar, r, t


def direct_sum(matrices: Sequence[np.ndarray]) -> np.ndarray:
    size = sum(a.shape[0] for a in matrices)
    out = np.zeros((size, size), dtype=complex)
    offset = 0
    for a in matrices:
        width = a.shape[0]
        out[offset : offset + width, offset : offset + width] = a
        offset += width
    return out


def spectral_commutant_basis(t: np.ndarray, tolerance: float = 1e-8) -> list[np.ndarray]:
    """Normalized-HS orthonormal matrix-unit basis of {T}'."""
    values, vectors = np.linalg.eig(t)
    groups: list[list[int]] = []
    representatives: list[complex] = []
    for index, value in enumerate(values):
        for group_index, representative in enumerate(representatives):
            if abs(value - representative) <= tolerance:
                groups[group_index].append(index)
                break
        else:
            representatives.append(value)
            groups.append([index])

    d = t.shape[0]
    basis: list[np.ndarray] = []
    for group in groups:
        # Eigenvectors returned by numpy need not be orthogonal inside a
        # repeated eigenspace.  QR gives a canonical orthonormal block.
        q, _ = np.linalg.qr(vectors[:, group])
        for row in range(q.shape[1]):
            for column in range(q.shape[1]):
                matrix_unit = np.outer(q[:, row], q[:, column].conj())
                basis.append(math.sqrt(d) * matrix_unit)
    return basis


def ad(u: np.ndarray, a: np.ndarray) -> np.ndarray:
    return u @ a @ u.conj().T


def reynolds(order_three: np.ndarray, a: np.ndarray) -> np.ndarray:
    return a + ad(order_three, a) + ad(order_three @ order_three, a)


def operator_matrix(
    basis: Sequence[np.ndarray], operator: Callable[[np.ndarray], np.ndarray]
) -> np.ndarray:
    d = basis[0].shape[0]
    return np.column_stack(
        [(operator(a) / math.sqrt(d)).reshape(-1, order="F") for a in basis]
    )


def smallest_singular(a: np.ndarray, tolerance: float = 1e-9) -> float:
    values = np.linalg.svd(a, compute_uv=False)
    if values.size == 0:
        return math.inf
    return float(values[-1]) if values[-1] > tolerance * max(1.0, float(values[0])) else 0.0


def koopman_regular_basis(d_matrix: np.ndarray, tolerance: float = 1e-9) -> tuple[np.ndarray, int]:
    # The codomain has dimension d^2 while the domain is only dim({T}').
    # The reduced SVD still returns a square right factor and avoids forming
    # a useless d^2 by d^2 left factor on the longer probes.
    _, singular, vh = np.linalg.svd(d_matrix, full_matrices=False)
    scale = max(1.0, float(singular[0]) if singular.size else 1.0)
    rank = int(np.count_nonzero(singular > tolerance * scale))
    return vh.conj().T[:, :rank], d_matrix.shape[1] - rank


def fourth_power_orbits(p: int) -> list[int]:
    unseen = set(range(p))
    lengths: list[int] = []
    while unseen:
        start = min(unseen)
        current = start
        orbit: list[int] = []
        while current not in orbit:
            orbit.append(current)
            unseen.discard(current)
            current = (4 * current) % p
        lengths.append(len(orbit))
    return sorted(lengths, reverse=True)


def nonlinear_pairwise_audit(x: np.ndarray, t: np.ndarray) -> dict[str, float]:
    """Check the exact finite-difference identity on one deterministic gauge."""
    d = x.shape[0]
    hermitian = (t + t.conj().T) / 2.0
    values, vectors = np.linalg.eigh(hermitian)
    phases = np.exp(1j * (0.37 * values + 0.19 * values * values))
    c = (vectors * phases) @ vectors.conj().T
    x_one = c @ x
    u = x_one @ x_one @ np.linalg.matrix_power(x, -2)
    v = (
        np.linalg.matrix_power(x_one @ t, 3)
        @ np.linalg.matrix_power(x @ t, -3)
    )
    alpha_u = ad(x @ t, u)
    identity_error = normalized_frobenius(v - c @ alpha_u)
    left = normalized_frobenius(c - np.eye(d, dtype=complex))
    right = normalized_frobenius(u - np.eye(d, dtype=complex)) + normalized_frobenius(
        v - np.eye(d, dtype=complex)
    )
    return {
        "identity_error": identity_error,
        "gauge_distance": left,
        "relative_row_bound": right,
        "metric_slack": right - left,
    }


def analyze_matrices(
    x: np.ndarray, r: np.ndarray, t: np.ndarray, metadata: dict[str, object]
) -> dict[str, object]:
    d = x.shape[0]
    identity = np.eye(d, dtype=complex)

    word_defects = {
        "x2": normalized_frobenius(x @ x - identity),
        "xr2": normalized_frobenius(np.linalg.matrix_power(x @ r, 2) - identity),
        "xt3": normalized_frobenius(np.linalg.matrix_power(x @ t, 3) - identity),
        "bs14": normalized_frobenius(r @ t @ r.conj().T - np.linalg.matrix_power(t, 4)),
        "xt2r3": normalized_frobenius(
            np.linalg.matrix_power(x @ t @ t @ r, 3) - identity
        ),
    }

    basis = spectral_commutant_basis(t)
    a_first = x @ t
    a_second = x @ t @ t @ r
    xr = x @ r

    rows = {
        "x2": operator_matrix(basis, lambda a: a + ad(x, a)),
        "xr2": operator_matrix(basis, lambda a: a + ad(xr, a)),
        "xt3": operator_matrix(basis, lambda a: reynolds(a_first, a)),
        "xt2r3": operator_matrix(basis, lambda a: reynolds(a_second, a)),
    }
    coboundary = operator_matrix(basis, lambda a: a - ad(r.conj().T, a))
    regular_basis, fixed_dimension = koopman_regular_basis(coboundary)

    row_sets = {
        "involution_plus_first_cubic": ("x2", "xt3"),
        "two_cubics": ("xt3", "xt2r3"),
        "all_x_rows": ("x2", "xr2", "xt3", "xt2r3"),
    }
    gaps = {}
    for name, selected in row_sets.items():
        stacked = np.vstack([rows[row] for row in selected]) @ regular_basis
        gaps[name] = smallest_singular(stacked)

    # Check that the quotient basis really makes inverse-Koopman energy the
    # Euclidean domain norm: D^dagger D is the identity on this basis.
    inverse = np.linalg.pinv(coboundary, rcond=1e-10)
    inverse_identity_error = float(
        np.linalg.norm(inverse @ coboundary @ regular_basis - regular_basis, 2)
    )

    return {
        **metadata,
        "dimension": d,
        "commutant_dimension": len(basis),
        "koopman_fixed_dimension": fixed_dimension,
        "koopman_regular_dimension": int(regular_basis.shape[1]),
        "word_defects": word_defects,
        "inverse_identity_operator_error": inverse_identity_error,
        "nonlinear_pairwise_audit": nonlinear_pairwise_audit(x, t),
        "quotient_row_gaps": gaps,
        "proved_floor_involution_plus_first_cubic": 1.0 / math.sqrt(2.0),
    }


def analyze(primes: Sequence[int]) -> dict[str, object]:
    endpoints = [endpoint(p) for p in primes]
    x = direct_sum([triple[0] for triple in endpoints])
    r = direct_sum([triple[1] for triple in endpoints])
    t = direct_sum([triple[2] for triple in endpoints])
    return analyze_matrices(
        x,
        r,
        t,
        {
            "model": "exact projective endpoint",
            "primes": list(primes),
            "fourth_power_orbit_lengths": {str(p): fourth_power_orbits(p) for p in primes},
        },
    )


def analyze_even_weil(p: int) -> dict[str, object]:
    x, r, t = even_weil_compression(p)
    return analyze_matrices(
        x,
        r,
        t,
        {
            "model": "compressed even Weil outlier",
            "prime": p,
            "fourth_power_orbit_lengths": {str(p): fourth_power_orbits(p)},
        },
    )


def parse_prime_block(raw: str) -> list[int]:
    values = [int(piece) for piece in raw.split(",") if piece]
    if not values:
        raise argparse.ArgumentTypeError("prime block must not be empty")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--blocks",
        nargs="+",
        type=parse_prime_block,
        default=[[5], [7], [11], [19], [23], [47], [7, 11]],
        help="comma-separated prime lists; a list with several primes is a heterogeneous direct sum",
    )
    parser.add_argument(
        "--even-weil",
        nargs="*",
        type=int,
        default=[],
        help="p = 1 mod 8 compressed even-Weil outliers",
    )
    parser.add_argument("--output")
    args = parser.parse_args()

    payload = {
        "status": "finite diagnostic; algebraic floor is proved in Cairn",
        "normalization": "normalized Hilbert--Schmidt",
        "rows": [analyze(block) for block in args.blocks]
        + [analyze_even_weil(p) for p in args.even_weil],
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
