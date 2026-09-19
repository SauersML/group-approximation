"""Spectral calibration for finite cohomological repair codes.

The live TRUE gate concerns degree-one circle cocycles, but any argument that
derives a uniform repair constant merely from a locally free sofic chart must
already work for the degree-zero repetition code on that chart.  This script
compares random two-generator Schreier graphs with exact Schreier graphs that
have the same local random structure inside two halves and only two cross-half
generator edges.

For each graph it records the first positive singular value of the incidence
operator and the binary defect/distance ratio of a half-space word.  The
bottleneck family is an adversarial control: it is still an exact finite F2
action, but local statistics do not see its macroscopic cut.
"""

import argparse
import json

import numpy as np
from scipy.sparse import coo_matrix, csgraph
from scipy.sparse.linalg import eigsh


def random_permutation(size, rng):
    return rng.permutation(size)


def bottleneck_permutations(size, rng):
    if size % 2:
        raise ValueError("bottleneck size must be even")
    half = size // 2
    permutations = []
    for generator in range(2):
        left = rng.permutation(half)
        right = half + rng.permutation(half)
        permutation = np.concatenate((left, right))
        if generator == 0:
            # Swapping two images preserves bijectivity and creates precisely
            # two directed cross-half generator edges.
            left_source = int(rng.integers(half))
            right_source = half + int(rng.integers(half))
            permutation[left_source], permutation[right_source] = (
                permutation[right_source], permutation[left_source])
        permutations.append(permutation)
    return permutations


def incidence(permutations):
    size = len(permutations[0])
    rows = []
    cols = []
    data = []
    edge = 0
    for permutation in permutations:
        for source, target in enumerate(permutation):
            rows.extend((edge, edge))
            cols.extend((source, int(target)))
            data.extend((-1.0, 1.0))
            edge += 1
    return coo_matrix((data, (rows, cols)),
                      shape=(edge, size)).tocsr()


def connected_components(incidence_matrix):
    adjacency = incidence_matrix.T @ incidence_matrix
    adjacency.setdiag(0)
    adjacency.eliminate_zeros()
    count, _ = csgraph.connected_components(adjacency, directed=False)
    return int(count)


def spectral_gap(incidence_matrix):
    laplacian = incidence_matrix.T @ incidence_matrix
    values = eigsh(laplacian, k=2, which="SM", return_eigenvectors=False,
                   tol=1e-9, maxiter=200000)
    values.sort()
    return float(np.sqrt(max(0.0, values[1])))


def half_word(permutations):
    size = len(permutations[0])
    half = size // 2
    word = np.zeros(size, dtype=np.uint8)
    word[half:] = 1
    violations = 0
    checks = 0
    for permutation in permutations:
        violations += int(np.count_nonzero(word != word[permutation]))
        checks += size
    distance = min(int(word.sum()), size - int(word.sum())) / size
    return {
        "check_defect": violations / checks,
        "distance_to_constants": distance,
        "distance_over_defect": (distance * checks / violations
                                 if violations else None),
    }


def instance(size, seed, family):
    rng = np.random.default_rng(seed)
    if family == "random":
        permutations = [random_permutation(size, rng) for _ in range(2)]
    else:
        permutations = bottleneck_permutations(size, rng)
    boundary = incidence(permutations)
    return {
        "family": family,
        "vertices": size,
        "seed": seed,
        "components": connected_components(boundary),
        "sigma_min_positive": spectral_gap(boundary),
        **half_word(permutations),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", type=int, nargs="+",
                        default=(256, 512, 1024, 2048, 4096))
    parser.add_argument("--seed", type=int, default=1729)
    args = parser.parse_args()
    for offset, size in enumerate(args.sizes):
        for family in ("random", "bottleneck"):
            print(json.dumps(instance(size, args.seed + offset, family)),
                  flush=True)


if __name__ == "__main__":
    main()
