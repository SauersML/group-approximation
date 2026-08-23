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


def full_matrix_operator(unitary: np.ndarray) -> np.ndarray:
    """Matrix of ``A -> Ad(unitary)(A)`` in column-major vectorization."""
    return np.kron(unitary.conj(), unitary)


def full_selector_linear_gap(
    x: np.ndarray, r: np.ndarray, t: np.ndarray, tolerance: float = 1e-9
) -> dict[str, object]:
    """Audit the genuinely constrained linearized selector.

    An arbitrary left tangent ``H`` changes the Weyl/inversion residual by
    ``(1-Ad(R^-1))H``.  Its projected minimum coboundary preimage is the
    regular part ``A`` of the conditional expectation of ``H`` onto
    ``{T}'``.  Write ``H=A+B``, where ``B`` is otherwise unrestricted.  For
    each prescribed ``A`` we eliminate the best possible ``B`` from the
    Iwahori row derivatives and report the resulting quotient singular
    value.  This detects cancellations that the gauge-only audit cannot see.

    The calculation is over the complexification of the matrix tangent
    space.  All row maps preserve the star decomposition, so this has the
    same lower gap as the Hermitian/skew-Hermitian real tangent problem.
    """
    d = x.shape[0]
    n = d * d
    identity = np.eye(n, dtype=complex)

    basis = spectral_commutant_basis(t)
    coboundary_on_z = operator_matrix(basis, lambda a: a - ad(r.conj().T, a))
    regular_coordinates, fixed_dimension = koopman_regular_basis(
        coboundary_on_z, tolerance=tolerance
    )
    z_basis = np.column_stack(
        [(a / math.sqrt(d)).reshape(-1, order="F") for a in basis]
    )
    regular_basis = z_basis @ regular_coordinates

    def torsion_row(unitary: np.ndarray, order: int) -> np.ndarray:
        conjugation = full_matrix_operator(unitary)
        out = identity.copy()
        power = identity.copy()
        for _ in range(1, order):
            power = power @ conjugation
            out += power
        return out

    row_matrices = {
        "x2": torsion_row(x, 2),
        "xr2": torsion_row(x @ r, 2),
        "xt3": torsion_row(x @ t, 3),
        "xt2r3": torsion_row(x @ t @ t @ r, 3),
    }
    row_sets = {
        "involution_plus_first_cubic": ("x2", "xt3"),
        "three_torsion_rows": ("x2", "xt3", "xt2r3"),
        "all_x_rows": ("x2", "xr2", "xt3", "xt2r3"),
    }

    gaps: dict[str, float] = {}
    cancellation_dimensions: dict[str, int] = {}
    for name, selected in row_sets.items():
        full_rows = np.vstack([row_matrices[row] for row in selected])
        prescribed = full_rows @ regular_basis

        # The other tangent directions are ker(A-coordinate).  Avoid forming
        # an explicit orthogonal-complement basis: L(I-BB*) has exactly the
        # same range as L restricted to that complement.
        cancellers = full_rows - prescribed @ regular_basis.conj().T
        u, singular, _ = np.linalg.svd(cancellers, full_matrices=False)
        scale = max(1.0, float(singular[0]) if singular.size else 1.0)
        rank = int(np.count_nonzero(singular > tolerance * scale))
        cancellation_dimensions[name] = rank
        if rank:
            effective = prescribed - u[:, :rank] @ (u[:, :rank].conj().T @ prescribed)
        else:
            effective = prescribed
        gaps[name] = smallest_singular(effective, tolerance=tolerance)

    return {
        "regular_gauge_dimension": int(regular_basis.shape[1]),
        "fixed_gauge_dimension": fixed_dimension,
        "quotient_row_gaps_after_arbitrary_endpoint_cancellation": gaps,
        "canceller_image_dimensions": cancellation_dimensions,
    }


def conjugation_counterpacket_audit(
    x: np.ndarray, r: np.ndarray, t: np.ndarray, target_operator_displacement: float = 1e-3
) -> dict[str, float]:
    """Probe the exact-first-vertex conjugation mechanism.

    For a low nonfixed Koopman mode ``a in {T}'``, conjugating only the Weyl
    endpoint by ``z=exp(i epsilon a)`` preserves ``X^2`` and ``(XT)^3``
    exactly.  The other two rows pay only the failure of ``z`` to commute
    with ``R``.  We project the resulting Weyl residual onto ``{T}'`` and
    report the norm of its minimum linear coboundary preimage.  Growth of
    preimage/row-defect is direct evidence against a dimension-free linear
    selector estimate; this function does not assert exact nonlinear
    coboundary solvability of the projected residual.
    """
    d = x.shape[0]
    identity = np.eye(d, dtype=complex)
    basis = spectral_commutant_basis(t)
    z_basis = np.column_stack(
        [(a / math.sqrt(d)).reshape(-1, order="F") for a in basis]
    )
    coboundary = operator_matrix(basis, lambda a: a - ad(r.conj().T, a))
    _, singular, vh = np.linalg.svd(coboundary, full_matrices=False)
    scale = max(1.0, float(singular[0]) if singular.size else 1.0)
    positive = np.flatnonzero(singular > 1e-9 * scale)
    if positive.size == 0:
        raise ValueError("the model has no regular Koopman direction")
    coordinates = vh.conj().T[:, positive[-1]]
    raw = sum(coefficient * matrix for coefficient, matrix in zip(coordinates, basis))
    hermitian_parts = ((raw + raw.conj().T) / 2.0, (raw - raw.conj().T) / (2.0j))
    a = max(hermitian_parts, key=normalized_frobenius)
    a = a / normalized_frobenius(a)
    operator_norm = float(np.linalg.norm(a, 2))
    epsilon = target_operator_displacement / max(1.0, operator_norm)
    values, vectors = np.linalg.eigh(a)
    z = (vectors * np.exp(1j * epsilon * values)) @ vectors.conj().T
    x_moved = z @ x @ z.conj().T

    defects = {
        "x2": normalized_frobenius(x_moved @ x_moved - identity),
        "xr2": normalized_frobenius(np.linalg.matrix_power(x_moved @ r, 2) - identity),
        "xt3": normalized_frobenius(np.linalg.matrix_power(x_moved @ t, 3) - identity),
        "xt2r3": normalized_frobenius(
            np.linalg.matrix_power(x_moved @ t @ t @ r, 3) - identity
        ),
    }
    total_row_defect = math.sqrt(sum(value * value for value in defects.values()))

    weyl = x_moved @ r @ x_moved.conj().T @ r - identity
    weyl_vector = (weyl / math.sqrt(d)).reshape(-1, order="F")
    solution = np.linalg.pinv(coboundary, rcond=1e-10) @ weyl_vector
    inverse_energy_norm = float(np.linalg.norm(solution))
    projected = z_basis @ (z_basis.conj().T @ weyl_vector)
    regular = coboundary @ solution
    fixed_holonomy_norm = float(np.linalg.norm(projected - regular))

    left_tangent = a - ad(x, a)
    tangent_vector = (left_tangent / math.sqrt(d)).reshape(-1, order="F")
    tangent_gauge_coordinates = z_basis.conj().T @ tangent_vector
    _, _, coboundary_vh = np.linalg.svd(coboundary, full_matrices=False)
    fixed_coordinates = coboundary_vh.conj().T[:, positive.size :]
    if fixed_coordinates.size:
        tangent_gauge_coordinates = tangent_gauge_coordinates - fixed_coordinates @ (
            fixed_coordinates.conj().T @ tangent_gauge_coordinates
        )
    tangent_gauge_norm = float(np.linalg.norm(tangent_gauge_coordinates))

    return {
        "smallest_positive_koopman_gap": float(singular[positive[-1]]),
        "mode_operator_norm_at_hs_norm_one": operator_norm,
        "epsilon": epsilon,
        "x2_defect": defects["x2"],
        "xr2_defect": defects["xr2"],
        "xt3_defect": defects["xt3"],
        "xt2r3_defect": defects["xt2r3"],
        "total_row_defect": total_row_defect,
        "minimum_projected_coboundary_preimage_norm": inverse_energy_norm,
        "preimage_to_row_ratio": inverse_energy_norm / max(total_row_defect, 1e-300),
        "projected_fixed_holonomy_norm": fixed_holonomy_norm,
        "linear_tangent_regular_gauge_norm": tangent_gauge_norm,
    }


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


def analyze(
    primes: Sequence[int], full_selector: bool = False, conjugation_counterpacket: bool = False
) -> dict[str, object]:
    endpoints = [endpoint(p) for p in primes]
    x = direct_sum([triple[0] for triple in endpoints])
    r = direct_sum([triple[1] for triple in endpoints])
    t = direct_sum([triple[2] for triple in endpoints])
    result = analyze_matrices(
        x,
        r,
        t,
        {
            "model": "exact projective endpoint",
            "primes": list(primes),
            "fourth_power_orbit_lengths": {str(p): fourth_power_orbits(p) for p in primes},
        },
    )
    if full_selector:
        result["full_selector_linear_audit"] = full_selector_linear_gap(x, r, t)
    if conjugation_counterpacket:
        result["conjugation_counterpacket_audit"] = conjugation_counterpacket_audit(x, r, t)
    return result


def analyze_even_weil(p: int, full_selector: bool = False) -> dict[str, object]:
    x, r, t = even_weil_compression(p)
    result = analyze_matrices(
        x,
        r,
        t,
        {
            "model": "compressed even Weil outlier",
            "prime": p,
            "fourth_power_orbit_lengths": {str(p): fourth_power_orbits(p)},
        },
    )
    if full_selector:
        result["full_selector_linear_audit"] = full_selector_linear_gap(x, r, t)
    return result


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
    parser.add_argument(
        "--full-selector",
        action="store_true",
        help="also eliminate arbitrary endpoint tangents in the linear selector audit",
    )
    parser.add_argument(
        "--conjugation-counterpacket",
        action="store_true",
        help="probe an exact-first-vertex low-Koopman conjugation packet",
    )
    parser.add_argument("--output")
    args = parser.parse_args()

    payload = {
        "status": "finite diagnostic; algebraic floor is proved in Cairn",
        "normalization": "normalized Hilbert--Schmidt",
        "rows": [
            analyze(
                block,
                full_selector=args.full_selector,
                conjugation_counterpacket=args.conjugation_counterpacket,
            )
            for block in args.blocks
        ]
        + [analyze_even_weil(p, full_selector=args.full_selector) for p in args.even_weil],
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
