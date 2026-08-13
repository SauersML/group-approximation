"""Lower-bound integral carry transversality on finite SL(3,Z) charts.

For A=d1, the squared row leverage h_c is the squared norm of the projection
of the integer cell vector e_c onto ran(A).  Hence

    dist(e_c, ran(A)) = sqrt(1-h_c).

If this is nonzero, e_c is not in ran(A) cap Z^cells, while its distance to
that integer lattice is at least one.  Therefore

    Theta(A) >= 1/sqrt(1-h_c).

The ratio is unchanged by normalized counting norms.  Pivoted dense QR is
used only for small calibration primes; the script reports the numerical
rank against the exact rank forced by H^1=0.
"""

import argparse
import json
import time

import numpy as np
from scipy.linalg import qr
from scipy.sparse.linalg import lsmr

from sl3_degree_one_spectrum import coboundaries, nonzero_vectors


def best_two_cell_carry(qmat, rank, names, vertices):
    projection = np.eye(qmat.shape[0]) - qmat[:, :rank] @ qmat[:, :rank].T
    diagonal = np.diag(projection)
    plus = diagonal[:, None] + diagonal[None, :] + 2.0 * projection
    minus = diagonal[:, None] + diagonal[None, :] - 2.0 * projection
    lower = np.tril_indices(len(diagonal))
    plus[lower] = np.inf
    minus[lower] = np.inf
    threshold = 1e-16
    plus[plus <= threshold] = np.inf
    minus[minus <= threshold] = np.inf
    plus_index = np.unravel_index(np.argmin(plus), plus.shape)
    minus_index = np.unravel_index(np.argmin(minus), minus.shape)
    if plus[plus_index] <= minus[minus_index]:
        first, second = map(int, plus_index)
        sign = 1
        squared_distance = float(plus[plus_index])
    else:
        first, second = map(int, minus_index)
        sign = -1
        squared_distance = float(minus[minus_index])

    def cell(index):
        return {
            "row": index,
            "relator": names[index // vertices],
            "start": index % vertices,
        }

    return {
        "first": cell(first),
        "second": cell(second),
        "second_coefficient": sign,
        "distance_to_real_range": float(np.sqrt(squared_distance)),
        "theta_two_cell_lower": float(1.0 / np.sqrt(squared_distance)),
    }


def run(prime, pair_search):
    started = time.time()
    names, vertices, d0, d1 = coboundaries(prime)
    expected_rank = d1.shape[1] - (vertices - 1)
    dense = d1.toarray()
    qmat, rmat, _pivots = qr(dense, mode="economic", pivoting=True,
                             overwrite_a=True, check_finite=False)
    diagonal = np.abs(np.diag(rmat))
    threshold = (max(dense.shape) * np.finfo(np.float64).eps *
                 (float(diagonal.max()) if len(diagonal) else 0.0))
    numerical_rank = int(np.sum(diagonal > threshold))
    if numerical_rank != expected_rank:
        raise AssertionError("rank %d differs from expected %d" %
                             (numerical_rank, expected_rank))

    leverage = np.sum(np.abs(qmat[:, :expected_rank]) ** 2, axis=1)
    distances = np.sqrt(np.maximum(0.0, 1.0 - leverage))
    positive = np.flatnonzero(distances > 1e-10)
    if not len(positive):
        raise AssertionError("every cell vector lies in the real range")
    best = int(positive[np.argmin(distances[positive])])
    cells_per_relator = vertices
    relation = best // cells_per_relator
    start = best % cells_per_relator
    per_relation = []
    for index, name in enumerate(names):
        values = leverage[index * vertices:(index + 1) * vertices]
        relation_distance = np.sqrt(np.maximum(0.0, 1.0 - values))
        eligible = relation_distance[relation_distance > 1e-10]
        per_relation.append({
            "name": name,
            "leverage_mean": float(np.mean(values)),
            "leverage_max_below_one": float(
                np.max(values[relation_distance > 1e-10])),
            "theta_basis_lower": float(1.0 / np.min(eligible)),
        })
    result = {
        "prime": prime,
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "expected_rank": expected_rank,
        "numerical_rank": numerical_rank,
        "rank_threshold": threshold,
        "leverage_sum": float(np.sum(leverage)),
        "leverage_quantiles": [
            [quantile, float(np.quantile(leverage, quantile))]
            for quantile in (0.0, 0.5, 0.9, 0.99, 1.0)
        ],
        "best_cell": {
            "row": best,
            "relator": names[relation],
            "start": start,
            "leverage": float(leverage[best]),
            "distance_to_real_range": float(distances[best]),
            "theta_basis_lower": float(1.0 / distances[best]),
        },
        "per_relation": per_relation,
        "elapsed_s": round(time.time() - started, 3),
    }
    if pair_search:
        result["best_two_cell_carry"] = best_two_cell_carry(
            qmat, expected_rank, names, vertices)
        result["elapsed_s"] = round(time.time() - started, 3)
    return result


def run_iterative(prime, tolerance, max_iterations):
    """Measure the fixed-axis torsion cell without forming a dense QR."""
    started = time.time()
    names, vertices, _d0, d1 = coboundaries(prime)
    points = nonzero_vectors(prime)
    matches = np.flatnonzero(np.all(points == np.array((0, 0, 1)), axis=1))
    if len(matches) != 1:
        raise AssertionError("failed to locate the fixed projective axis")
    start = int(matches[0])
    relation = names.index("crw_torsion")
    row = relation * vertices + start
    target = np.zeros(d1.shape[0], dtype=np.float64)
    target[row] = 1.0
    solution = lsmr(d1, target, atol=tolerance, btol=tolerance,
                    maxiter=max_iterations)
    residual = target - d1 @ solution[0]
    distance = float(np.linalg.norm(residual))
    normal_error = float(np.linalg.norm(d1.T @ residual))
    return {
        "prime": prime,
        "method": "lsmr_fixed_axis_torsion_cell",
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "row": row,
        "start": start,
        "distance_to_real_range": distance,
        "leverage": float(1.0 - distance * distance),
        "theta_basis_lower": float(1.0 / distance),
        "normal_equation_error": normal_error,
        "iterations": int(solution[2]),
        "lsmr_stop_code": int(solution[1]),
        "lsmr_condition_estimate": float(solution[6]),
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", required=True)
    parser.add_argument("--iterative", action="store_true")
    parser.add_argument("--pair-search", action="store_true")
    parser.add_argument("--tolerance", type=float, default=1e-12)
    parser.add_argument("--max-iterations", type=int, default=20000)
    args = parser.parse_args()
    for prime in args.primes:
        result = (run_iterative(prime, args.tolerance, args.max_iterations)
                  if args.iterative else run(prime, args.pair_search))
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
