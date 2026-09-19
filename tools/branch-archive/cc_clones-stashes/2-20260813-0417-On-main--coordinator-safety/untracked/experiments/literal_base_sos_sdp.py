"""Numerical SDP discovery for the proof-carrying literal-base quotient.

This imports ``literal_base_laplacian_sos`` for its relator-tracked word
reductions.  The numerical Gram matrix produced here is never a proof: it
must be rationalized, exactly replayed, and discharged through the Lean
certificate checker.
"""

import argparse
import json
import time

import cvxpy as cp
import numpy as np

import literal_base_laplacian_sos as literal


def install_inverse_action_rules():
    """Add certified `A v^-1 -> (A v A^-1)^-1 A` rewrites.

    Each rule is a conjugate of the inverse of the corresponding displayed
    action relator.  `Rule.validate` replays that identity in the free group
    before the rule can enter the reducer.
    """
    derived = []
    for relator_index in range(11, 20):
        relator = literal.RELATORS[relator_index]
        acting = relator.lhs[:1]
        source = relator.lhs[1:]
        image = relator.rhs[:-1]
        if len(acting) != 1 or len(source) != 1 \
                or relator.rhs[-1:] != acting:
            raise AssertionError("unexpected action-relator shape")
        rule = literal.Rule(
            acting + literal.inverse(source),
            literal.inverse(image) + acting,
            relator_index,
            inverted=True,
            local_conjugator=literal.inverse(image),
        )
        rule.validate()
        derived.append(rule)
    literal.RULES += tuple(derived)


install_inverse_action_rules()


class CachedReductionRegistry(literal.ReductionRegistry):
    """Memoize exact relator-replay reductions by freely reduced input."""

    def __init__(self):
        super().__init__()
        self._cache = {}

    def reduce(self, word):
        original = literal.free_reduce(word)
        cached = self._cache.get(original)
        if cached is not None:
            return cached
        reduced, atoms = literal.reduce_with_certificate(original)
        self._reductions.setdefault((original, reduced), atoms)
        self._cache[original] = reduced
        return reduced


def prepare(radius):
    started = time.time()
    registry = CachedReductionRegistry()
    support = literal.ball(radius, registry)
    pairs = literal.coefficient_pairs(support, registry)
    delta = literal.laplacian(registry)
    delta_square = literal.ring_product(delta, delta, registry)
    keys = sorted(set(pairs) | set(delta) | set(delta_square))
    return started, registry, support, pairs, delta, delta_square, keys


def describe_ball(radius):
    started = time.time()
    registry = CachedReductionRegistry()
    support = literal.ball(radius, registry)
    return {
        "radius": radius,
        "support": len(support),
        "checked_reductions": len(registry.reductions),
        "total_elapsed_s": round(time.time() - started, 3),
    }


def describe(radius):
    (started, registry, support, pairs, delta, delta_square,
     keys) = prepare(radius)
    return {
        "radius": radius,
        "support": len(support),
        "coefficient_classes": len(keys),
        "pair_product_groups": len(pairs),
        "delta_support": len(delta),
        "delta_square_support": len(delta_square),
        "checked_reductions": len(registry.reductions),
        "total_elapsed_s": round(time.time() - started, 3),
    }


def solve(radius, max_iterations, tolerance, gram_output,
          reduction_output):
    (started, registry, support, pairs, delta, delta_square,
     keys) = prepare(radius)
    dimension = len(support)
    gram = cp.Variable((dimension, dimension), symmetric=True)
    gap = cp.Variable()
    constraints = [gram >> 0, gram @ np.ones(dimension) == 0]
    for word in keys:
        locations = pairs.get(word, ())
        expression = (cp.sum(cp.hstack([gram[i, j] for i, j in locations]))
                      if locations else 0.0)
        constraints.append(
            expression == float(delta_square.get(word, 0))
            - gap * float(delta.get(word, 0))
        )
    problem = cp.Problem(cp.Maximize(gap), constraints)
    setup_elapsed = time.time() - started
    problem.solve(
        solver=cp.SCS,
        eps=tolerance,
        max_iters=max_iterations,
        verbose=False,
        normalize=True,
        acceleration_lookback=10,
    )
    if gram.value is not None and gram_output:
        np.save(gram_output, gram.value)
    if reduction_output:
        with open(reduction_output, "w", encoding="utf-8") as handle:
            json.dump(literal.certificate_json(registry), handle,
                      sort_keys=True)
            handle.write("\n")
    result = {
        "status": problem.status,
        "gap": None if gap.value is None else float(gap.value),
        "radius": radius,
        "support": dimension,
        "coefficient_classes": len(keys),
        "constraints": len(constraints),
        "checked_reductions": len(registry.reductions),
        "setup_elapsed_s": round(setup_elapsed, 3),
        "total_elapsed_s": round(time.time() - started, 3),
        "solver_iterations": problem.solver_stats.num_iters,
        "solver_time_s": problem.solver_stats.solve_time,
    }
    if gram.value is not None:
        eigenvalues = np.linalg.eigvalsh(
            0.5 * (gram.value + gram.value.T))
        result.update({
            "gram_min_eigenvalue": float(eigenvalues[0]),
            "gram_max_eigenvalue": float(eigenvalues[-1]),
            "gram_rank_at_1e-7": int(np.sum(eigenvalues > 1e-7)),
            "augmentation_defect": float(np.max(np.abs(
                gram.value @ np.ones(dimension)))),
            "max_constraint_violation": float(max(
                np.max(np.abs(constraint.violation()))
                for constraint in constraints
            )),
        })
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--max-iterations", type=int, default=5000)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    parser.add_argument("--gram-output")
    parser.add_argument("--reduction-output")
    parser.add_argument("--result-output")
    parser.add_argument("--ball-only", action="store_true")
    parser.add_argument("--describe-only", action="store_true")
    args = parser.parse_args()
    if args.ball_only:
        print(json.dumps(describe_ball(args.radius), sort_keys=True))
        return
    if args.describe_only:
        print(json.dumps(describe(args.radius), sort_keys=True))
        return
    result = solve(
        args.radius,
        args.max_iterations,
        args.tolerance,
        args.gram_output,
        args.reduction_output,
    )
    rendered = json.dumps(result, sort_keys=True)
    if args.result_output:
        with open(args.result_output, "w", encoding="utf-8") as handle:
            handle.write(rendered)
            handle.write("\n")
    print(rendered)


if __name__ == "__main__":
    main()
