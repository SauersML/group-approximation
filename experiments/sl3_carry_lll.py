"""LLL search for coordinated integral carries on SL(3,Z) charts.

Restrict integer carries to the CRW torsion-cell coordinates.  If Q spans
ran(d1), the residual columns (I-QQ*)e_c generate their projections to
ran(d1)^perp.  LLL is applied to the integer embedding

    z |-> (round(scale * (I-QQ*)z), z).

Every returned integer z is then evaluated against the unrounded orthogonal
projection.  A nonzero residual gives the rigorous-form lower-bound pattern
Theta >= 1/||projection(z)||, although the reported norm is numerical and
must be interval-certified before being used as a proof.
"""

import argparse
import hashlib
import json
import time

import numpy as np
from fpylll import IntegerMatrix, LLL
from scipy.linalg import qr

from sl3_degree_one_spectrum import coboundaries


def run(prime, scale, delta, all_cells):
    started = time.time()
    names, vertices, _d0, d1 = coboundaries(prime)
    expected_rank = d1.shape[1] - (vertices - 1)
    dense = d1.toarray()
    qmat, rmat, _pivots = qr(dense, mode="economic", pivoting=True,
                             overwrite_a=True, check_finite=False)
    diagonal = np.abs(np.diag(rmat))
    threshold = (max(dense.shape) * np.finfo(np.float64).eps *
                 float(diagonal.max()))
    numerical_rank = int(np.sum(diagonal > threshold))
    if numerical_rank != expected_rank:
        raise AssertionError("unexpected relator rank")
    qmat = qmat[:, :expected_rank]

    relation = names.index("crw_torsion")
    rows = (np.arange(d1.shape[0]) if all_cells else
            np.arange(relation * vertices, (relation + 1) * vertices))
    generator_count = len(rows)
    residual_columns = -qmat @ qmat[rows, :].T
    residual_columns[rows, np.arange(generator_count)] += 1.0
    embedded = np.rint(scale * residual_columns.T).astype(np.int64)
    lattice_rows = np.concatenate(
        (embedded, np.eye(generator_count, dtype=np.int64)), axis=1)
    lattice = IntegerMatrix.from_matrix(lattice_rows.tolist())
    LLL.reduction(lattice, delta=delta)

    candidates = []
    for row_index in range(generator_count):
        coefficients = np.array(
            [int(lattice[row_index, d1.shape[0] + column])
             for column in range(generator_count)], dtype=np.int64)
        if not np.any(coefficients):
            continue
        carry = np.zeros(d1.shape[0], dtype=np.float64)
        carry[rows] = coefficients
        residual = carry - qmat @ (qmat.T @ carry)
        distance = float(np.linalg.norm(residual))
        if distance <= 1e-9:
            continue
        support = np.flatnonzero(coefficients)
        coefficient_hash = hashlib.sha256(
            coefficients.astype("<i8", copy=False).tobytes()).hexdigest()
        preview = support[:32]
        candidates.append({
            "basis_row": row_index,
            "distance_to_real_range": distance,
            "theta_lower": float(1.0 / distance),
            "coefficient_l1": int(np.sum(np.abs(coefficients))),
            "coefficient_l2": float(np.linalg.norm(coefficients)),
            "coefficient_max": int(np.max(np.abs(coefficients))),
            "coefficient_support": int(len(support)),
            "coefficient_sha256": coefficient_hash,
            "nonzero_coefficients_preview": [
                [int(rows[index]), int(coefficients[index])]
                for index in preview
            ],
            "coefficients_truncated": bool(len(support) > len(preview)),
        })
    candidates.sort(key=lambda item: item["distance_to_real_range"])
    return {
        "prime": prime,
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "candidate_kind": "all_cells" if all_cells else "torsion_cells",
        "lattice_generators": generator_count,
        "projection_rank": expected_rank,
        "scale": scale,
        "lll_delta": delta,
        "nonexact_reduced_rows": len(candidates),
        "best": candidates[0] if candidates else None,
        "top_five": candidates[:5],
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", required=True)
    parser.add_argument("--scale", type=int, default=100000)
    parser.add_argument("--delta", type=float, default=0.99)
    parser.add_argument("--all-cells", action="store_true")
    args = parser.parse_args()
    for prime in args.primes:
        print(json.dumps(run(prime, args.scale, args.delta,
                             args.all_cells)), flush=True)


if __name__ == "__main__":
    main()
