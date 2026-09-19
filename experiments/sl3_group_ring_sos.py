"""Search for a group-ring SOS certificate for the SL(3,Z) Hodge gap.

For the fixed six-generator, thirteen-relator presentation used by
sl3_degree_one_spectrum.py, construct the degree-one Hodge matrix Delta over
R[SL_3(Z)] exactly.  Given a finite group support E, solve

    maximize c  subject to  Delta - c I = V* P V,  P >= 0,

where V contains e_i g for i=1,...,6 and g in E.  Group elements are
canonicalized by their exact integral 3x3 matrices.  A positive numerical
solution is only a candidate; its Gram matrix must be rationalized and the
coefficient identity and positivity certified exactly before it is a proof.
"""

import argparse
import json
import time

import numpy as np

from sl3_degree_one_spectrum import ROOTS, presentation_relators


IDENTITY = (1, 0, 0, 0, 1, 0, 0, 0, 1)


def matrix_multiply(left, right):
    return tuple(sum(left[3 * i + k] * right[3 * k + j]
                     for k in range(3))
                 for i in range(3) for j in range(3))


def matrix_inverse(matrix):
    a, b, c, d, e, f, g, h, i = matrix
    inverse = (
        e * i - f * h, c * h - b * i, b * f - c * e,
        f * g - d * i, a * i - c * g, c * d - a * f,
        d * h - e * g, b * g - a * h, a * e - b * d,
    )
    if matrix_multiply(matrix, inverse) != IDENTITY:
        raise AssertionError("matrix is not in SL_3(Z)")
    return inverse


def generators():
    answer = []
    for row, column in ROOTS:
        matrix = list(IDENTITY)
        matrix[3 * row + column] = 1
        answer.append(tuple(matrix))
    return answer


def word_value(word, generator_matrices):
    value = IDENTITY
    for generator, sign in word:
        factor = (generator_matrices[generator] if sign == 1 else
                  matrix_inverse(generator_matrices[generator]))
        value = matrix_multiply(value, factor)
    return value


def ring_add_term(element, group, coefficient):
    if coefficient:
        element[group] = element.get(group, 0) + coefficient
        if element[group] == 0:
            del element[group]


def ring_adjoint(element):
    return {matrix_inverse(group): coefficient
            for group, coefficient in element.items()}


def ring_product(left, right):
    answer = {}
    for first, first_coefficient in left.items():
        for second, second_coefficient in right.items():
            ring_add_term(answer, matrix_multiply(first, second),
                          first_coefficient * second_coefficient)
    return answer


def hodge_matrix():
    names, relators = presentation_relators()
    generator_matrices = generators()
    if any(word_value(word, generator_matrices) != IDENTITY
           for word in relators):
        raise AssertionError("presentation relator is nontrivial")

    d0 = []
    for generator in generator_matrices:
        entry = {generator: 1, IDENTITY: -1}
        d0.append(entry)

    d1 = []
    # d1* d1 uses relator prefixes.  The positive factorization of d0 d0*
    # uses the row d0*, so its monomial support contains the inverse
    # generators as well as the identity.
    prefix_support = {IDENTITY}
    prefix_support.update(matrix_inverse(group)
                          for group in generator_matrices)
    for word in relators:
        row = [{} for _ in ROOTS]
        prefix = IDENTITY
        for generator, sign in word:
            if sign == 1:
                edge_prefix = prefix
                prefix = matrix_multiply(prefix,
                                         generator_matrices[generator])
                coefficient = 1
            else:
                prefix = matrix_multiply(
                    prefix, matrix_inverse(generator_matrices[generator]))
                edge_prefix = prefix
                coefficient = -1
            ring_add_term(row[generator], edge_prefix, coefficient)
            prefix_support.add(edge_prefix)
        if prefix != IDENTITY:
            raise AssertionError("relator prefix did not close")
        d1.append(row)

    delta = [[{} for _ in ROOTS] for _ in ROOTS]
    for left in range(len(ROOTS)):
        for right in range(len(ROOTS)):
            entry = {}
            for row in d1:
                product = ring_product(ring_adjoint(row[left]), row[right])
                for group, coefficient in product.items():
                    ring_add_term(entry, group, coefficient)
            product = ring_product(d0[left], ring_adjoint(d0[right]))
            for group, coefficient in product.items():
                ring_add_term(entry, group, coefficient)
            delta[left][right] = entry

    for left in range(len(ROOTS)):
        for right in range(len(ROOTS)):
            if delta[left][right] != ring_adjoint(delta[right][left]):
                raise AssertionError("Hodge matrix is not self-adjoint")
    return names, generator_matrices, d0, d1, delta, prefix_support


def expanded_support(prefix_support, generator_matrices, radius):
    support = set(prefix_support)
    frontier = set(prefix_support)
    steps = generator_matrices + [matrix_inverse(group)
                                  for group in generator_matrices]
    for _ in range(radius):
        new_frontier = set()
        for group in frontier:
            for step in steps:
                product = matrix_multiply(group, step)
                if product not in support:
                    new_frontier.add(product)
        support.update(new_frontier)
        frontier = new_frontier
    return sorted(support)


def coefficient_pairs(support):
    pairs = {}
    inverses = [matrix_inverse(group) for group in support]
    for left, inverse in enumerate(inverses):
        for right, group in enumerate(support):
            product = matrix_multiply(inverse, group)
            pairs.setdefault(product, []).append((left, right))
    return pairs


def solve(radius, max_iterations, tolerance, gram_output):
    import cvxpy as cp

    started = time.time()
    (names, generator_matrices, _d0, _d1, delta,
     prefix_support) = hodge_matrix()
    support = expanded_support(prefix_support, generator_matrices, radius)
    pairs = coefficient_pairs(support)
    group_keys = set(pairs)
    for row in delta:
        for entry in row:
            group_keys.update(entry)
    group_keys = sorted(group_keys)

    block_size = len(support)
    dimension = len(ROOTS) * block_size
    gram = cp.Variable((dimension, dimension), symmetric=True)
    gap = cp.Variable()
    constraints = [gram >> 0]
    for left in range(len(ROOTS)):
        left_offset = left * block_size
        for right in range(len(ROOTS)):
            right_offset = right * block_size
            target_entry = delta[left][right]
            for group in group_keys:
                locations = pairs.get(group, ())
                if locations:
                    expression = cp.sum(cp.hstack([
                        gram[left_offset + source,
                             right_offset + target]
                        for source, target in locations
                    ]))
                else:
                    expression = 0.0
                target = float(target_entry.get(group, 0))
                if left == right and group == IDENTITY:
                    target -= gap
                constraints.append(expression == target)

    problem = cp.Problem(cp.Maximize(gap), constraints)
    setup_elapsed = time.time() - started
    problem.solve(solver=cp.SCS, eps=tolerance, max_iters=max_iterations,
                  verbose=False, normalize=True, acceleration_lookback=10)
    gram_value = gram.value
    if gram_output and gram_value is not None:
        np.save(gram_output, gram_value)
    result = {
        "status": problem.status,
        "gap": None if gap.value is None else float(gap.value),
        "objective": None if problem.value is None else float(problem.value),
        "radius": radius,
        "generators": len(ROOTS),
        "relators": len(names),
        "prefix_support": len(prefix_support),
        "support": block_size,
        "gram_dimension": dimension,
        "group_coefficients": len(group_keys),
        "constraints": len(constraints),
        "setup_elapsed_s": round(setup_elapsed, 3),
        "total_elapsed_s": round(time.time() - started, 3),
        "solver_iterations": problem.solver_stats.num_iters,
        "solver_time_s": problem.solver_stats.solve_time,
    }
    if gram_value is not None:
        eigenvalues = np.linalg.eigvalsh(
            0.5 * (gram_value + gram_value.T))
        result["gram_min_eigenvalue"] = float(eigenvalues[0])
        result["gram_max_eigenvalue"] = float(eigenvalues[-1])
        result["gram_rank_at_1e-7"] = int(np.sum(eigenvalues > 1e-7))
        result["max_constraint_violation"] = float(
            max(abs(constraint.violation()).max() for constraint in constraints))
    return result


def describe(radius):
    (names, generator_matrices, _d0, _d1, delta,
     prefix_support) = hodge_matrix()
    support = expanded_support(prefix_support, generator_matrices, radius)
    pairs = coefficient_pairs(support)
    target_groups = set()
    target_terms = 0
    for row in delta:
        for entry in row:
            target_groups.update(entry)
            target_terms += len(entry)
    return {
        "radius": radius,
        "generators": len(ROOTS),
        "relators": len(names),
        "prefix_support": len(prefix_support),
        "support": len(support),
        "gram_dimension": len(ROOTS) * len(support),
        "pair_product_groups": len(pairs),
        "target_groups": len(target_groups),
        "target_terms": target_terms,
    }


def validate_finite_action(prime):
    """Compare the group-ring operator with the direct Schreier complex."""
    from scipy.sparse import bmat, coo_matrix, csr_matrix
    from sl3_degree_one_spectrum import coboundaries, nonzero_vectors

    (_names, _generator_matrices, _d0, _d1, delta,
     _prefix_support) = hodge_matrix()
    points = nonzero_vectors(prime)
    point_index = {tuple(point): index
                   for index, point in enumerate(points.tolist())}
    cache = {}

    def representation(group):
        if group not in cache:
            matrix = np.asarray(group, dtype=np.int64).reshape((3, 3)) % prime
            targets = [point_index[tuple(((point @ matrix) % prime).tolist())]
                       for point in points]
            rows = np.arange(len(points), dtype=np.int64)
            cache[group] = coo_matrix(
                (np.ones(len(points)), (rows, np.asarray(targets))),
                shape=(len(points), len(points))).tocsr()
        return cache[group]

    blocks = []
    for row in delta:
        block_row = []
        for entry in row:
            value = csr_matrix((len(points), len(points)), dtype=np.float64)
            for group, coefficient in entry.items():
                value = value + coefficient * representation(group)
            block_row.append(value)
        blocks.append(block_row)
    evaluated = bmat(blocks, format="csr")
    _names, _vertices, direct_d0, direct_d1 = coboundaries(prime)
    direct = direct_d1.T @ direct_d1 + direct_d0 @ direct_d0.T
    difference = evaluated - direct
    return {
        "prime": prime,
        "dimension": int(direct.shape[0]),
        "group_elements_evaluated": len(cache),
        "difference_nnz": int(difference.nnz),
        "max_abs_difference": (float(np.max(np.abs(difference.data)))
                               if difference.nnz else 0.0),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=0)
    parser.add_argument("--describe", action="store_true")
    parser.add_argument("--validate-prime", type=int)
    parser.add_argument("--max-iterations", type=int, default=20000)
    parser.add_argument("--tolerance", type=float, default=1e-6)
    parser.add_argument("--gram-output")
    args = parser.parse_args()
    if args.validate_prime is not None:
        print(json.dumps(validate_finite_action(args.validate_prime)))
    elif args.describe:
        print(json.dumps(describe(args.radius)))
    else:
        print(json.dumps(solve(args.radius, args.max_iterations,
                               args.tolerance, args.gram_output)))


if __name__ == "__main__":
    main()
