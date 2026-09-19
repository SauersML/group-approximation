#!/usr/bin/env python3
"""Probe the uniform parabolic/interior splitting for Iwahori cohomology.

For the P^1(F_p) permutation representation rho, form M=Ad rho and the
fixed-generator cocycle space Z^1(SL_2(Z),M) using the same presentation as
iwahori_linearized_gap.py.  Quotient orthogonally by coboundaries.  Restriction
to the parabolic <u> is c |-> P_(M^u)c(u), since M/(u-1)M is canonically M^u
for a unitary representation.  The smallest nonzero singular value of this
map is exactly the angle controlling a bounded Eisenstein lift in this model.

Run on MSI; the default screen is deliberately bounded.
"""

from __future__ import annotations

import argparse
import json
import sys

import numpy as np

from iwahori_linearized_gap import (
    ad,
    cocycle_word_map,
    nullspace,
    sl2_perm_rep_P1,
)


def range_basis(matrix: np.ndarray, tol: float = 1e-9) -> np.ndarray:
    """Orthonormal basis of the column space, using the small Gram matrix."""
    gram = matrix.conj().T @ matrix
    values, vectors = np.linalg.eigh(gram)
    scale = max(1.0, float(values[-1]) if len(values) else 1.0)
    keep = values > (tol**2) * scale * 1e4
    if not np.any(keep):
        return np.zeros((matrix.shape[0], 0), dtype=matrix.dtype)
    basis = matrix @ (vectors[:, keep] / np.sqrt(values[keep]))
    return basis


def analyze(p: int) -> dict[str, object]:
    rho, d = sl2_perm_rep_P1(p)
    u = [[1, 1], [0, 1]]
    v = [[1, 0], [1, 1]]
    au, av = ad(rho(u)), ad(rho(v))
    d2 = d * d
    identity = np.eye(d2)

    # SL_2(Z) relators in the unipotent generators u,v.
    r1 = [(0, 1), (1, -1), (0, 1)] * 4
    r2 = [(0, 1), (1, -1), (0, 1), (1, 1), (0, -1), (1, 1)]
    relations = np.vstack(
        [cocycle_word_map([au, av], r1), cocycle_word_map([au, av], r2)]
    )
    z_basis, _ = nullspace(relations)

    # Coboundaries x |-> ((Ad u-I)x,(Ad v-I)x), already contained in Z^1.
    coboundary = np.vstack([au - identity, av - identity])
    b_basis = range_basis(coboundary)
    h_coords, _ = nullspace(b_basis.conj().T @ z_basis)
    h_basis = z_basis @ h_coords

    # Unitary coinvariants M/(u-1)M are isometric to invariants M^u.
    u_invariants, _ = nullspace(au - identity)
    boundary = u_invariants.conj().T @ h_basis[:d2, :]
    singular = np.linalg.svd(boundary, compute_uv=False)
    scale = max(1.0, float(singular[0]) if len(singular) else 1.0)
    rank = int(np.sum(singular > 1e-8 * scale))
    nonzero = singular[:rank]

    return {
        "p": p,
        "d": d,
        "dim_Z1": int(z_basis.shape[1]),
        "dim_B1": int(b_basis.shape[1]),
        "dim_H1": int(h_basis.shape[1]),
        "boundary_rank": rank,
        "boundary_kernel": int(h_basis.shape[1] - rank),
        "sigma_min_nonzero": float(nonzero[-1]) if rank else None,
        "sigma_max": float(nonzero[0]) if rank else None,
        "smallest5": nonzero[max(0, rank - 5) : rank].tolist(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes", nargs="+", type=int, default=[3, 5, 7, 11, 13, 17, 19, 23])
    parser.add_argument("--output", default="iwahori-parabolic-split.json")
    args = parser.parse_args()

    results = []
    for prime in args.primes:
        result = analyze(prime)
        results.append(result)
        print(json.dumps(result))
        sys.stdout.flush()
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(results, handle, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()
