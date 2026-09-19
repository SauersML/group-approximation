"""Numerically extract the harmonic two-plane of a projective Shapiro chart.

The exported boundaries use row-vector conventions:

    d2 : C2 -> C1,  d3 : C3 -> C2.

Consequently the real harmonic space in C2 is the kernel of

    Delta2 = d2*d2^T + d3^T*d3.

This probe never materializes Delta2.  It applies the four sparse boundary
products through a LinearOperator and reports independently computed
residuals for both harmonic equations.  Run it on MSI with Sage's Python.
"""

import argparse
import hashlib
import json
import time

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import LinearOperator, lobpcg


def read_boundary(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        header = stream.readline()
        digest.update(header)
        rows, columns = map(int, header.split())
        raw = stream.read()
        digest.update(raw)
    if raw:
        entries = np.fromstring(raw.decode("ascii"), dtype=np.int64, sep=" ")
        if entries.size % 3:
            raise AssertionError("sparse boundary has an incomplete entry")
        entries = entries.reshape((-1, 3))
        matrix = sparse.coo_matrix(
            (entries[:, 2].astype(np.float64),
             (entries[:, 0], entries[:, 1])),
            shape=(rows, columns)).tocsr()
        matrix.sum_duplicates()
        matrix.eliminate_zeros()
    else:
        matrix = sparse.csr_matrix((rows, columns), dtype=np.float64)
    return matrix, digest.hexdigest()


def quantiles(values):
    levels = (0.0, 0.25, 0.5, 0.75, 0.9, 0.99, 1.0)
    measured = np.quantile(values, levels)
    return {str(level): float(value)
            for level, value in zip(levels, measured)}


def run(prefix, chart_prime, block_size, vectors, tolerance, max_iterations,
        seed, vector_output):
    started = time.perf_counter()
    d2, d2_hash = read_boundary(prefix + "-d2.tsv")
    d3, d3_hash = read_boundary(prefix + "-d3.tsv")
    if d3.shape[1] != d2.shape[0]:
        raise AssertionError("boundary dimensions do not compose")
    cells = d2.shape[0]

    def laplacian_product(values):
        return d2 @ (d2.T @ values) + d3.T @ (d3 @ values)

    laplacian = LinearOperator(
        (cells, cells), matvec=laplacian_product,
        matmat=laplacian_product, dtype=np.float64)
    diagonal = (
        np.asarray(d2.multiply(d2).sum(axis=1)).ravel()
        + np.asarray(d3.multiply(d3).sum(axis=0)).ravel())
    if np.any(diagonal <= 0):
        raise AssertionError("Hodge diagonal is not positive")

    def precondition(values):
        if values.ndim == 1:
            return values / diagonal
        return values / diagonal[:, None]

    preconditioner = LinearOperator(
        (cells, cells), matvec=precondition,
        matmat=precondition, dtype=np.float64)
    random = np.random.default_rng(seed)
    initial = random.standard_normal((cells, vectors))
    eigenvalues, eigenvectors, residual_history = lobpcg(
        laplacian, initial, M=preconditioner, largest=False,
        tol=tolerance, maxiter=max_iterations,
        retResidualNormsHistory=True)
    order = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[order]
    eigenvectors = eigenvectors[:, order]
    residuals = np.linalg.norm(
        laplacian_product(eigenvectors) - eigenvectors * eigenvalues,
        axis=0)
    cycle_residuals = np.linalg.norm(d2.T @ eigenvectors, axis=0)
    boundary_residuals = np.linalg.norm(d3 @ eigenvectors, axis=0)

    harmonic_dimension = int(np.count_nonzero(
        np.maximum(cycle_residuals, boundary_residuals)
        <= np.sqrt(tolerance)))
    harmonic = eigenvectors[:, :harmonic_dimension]
    leverage = np.sum(harmonic * harmonic, axis=1)
    if cells % block_size:
        raise AssertionError("cell dimension is not divisible by block size")
    orbit_size = cells // block_size
    block_leverage = leverage.reshape((block_size, orbit_size))
    block_statistics = []
    for index, values in enumerate(block_leverage):
        block_statistics.append({
            "block": index,
            "sum": float(np.sum(values)),
            "mean": float(np.mean(values)),
            "standard_deviation": float(np.std(values)),
            "minimum": float(np.min(values)),
            "maximum": float(np.max(values)),
        })

    if vector_output:
        np.savez_compressed(
            vector_output, harmonic=harmonic, eigenvalues=eigenvalues,
            cycle_residuals=cycle_residuals,
            boundary_residuals=boundary_residuals,
            leverage=leverage)

    return {
        "chart": "projective",
        "chart_prime": chart_prime,
        "chain_dimensions": [d2.shape[1], cells, d3.shape[0]],
        "d2_nnz": int(d2.nnz),
        "d3_nnz": int(d3.nnz),
        "d2_sha256": d2_hash,
        "d3_sha256": d3_hash,
        "solver": "scipy_lobpcg_diagonal_preconditioner",
        "requested_vectors": vectors,
        "tolerance": tolerance,
        "max_iterations": max_iterations,
        "iterations": len(residual_history) - 1,
        "eigenvalues": [float(value) for value in eigenvalues],
        "eigen_residuals": [float(value) for value in residuals],
        "cycle_residuals": [float(value) for value in cycle_residuals],
        "boundary_residuals": [float(value) for value in boundary_residuals],
        "detected_harmonic_dimension": harmonic_dimension,
        "harmonic_leverage_sum": float(np.sum(leverage)),
        "harmonic_leverage_quantiles": quantiles(leverage),
        "harmonic_block_leverage": block_statistics,
        "elapsed_seconds": time.perf_counter() - started,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--blocks", type=int, default=10)
    parser.add_argument("--vectors", type=int, default=6)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    parser.add_argument("--max-iterations", type=int, default=500)
    parser.add_argument("--seed", type=int, default=20260811)
    parser.add_argument("--vector-output")
    args = parser.parse_args()
    result = run(
        args.prefix, args.prime, args.blocks, args.vectors, args.tolerance,
        args.max_iterations, args.seed, args.vector_output)
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
