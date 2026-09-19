"""Small-support Hodge-SOS probe for the literal affine presentation.

The six generators and twenty relators are imported from
``literal_base_laplacian_sos``.  All group-ring products are canonicalized by
that module's proof-carrying relator reducer: every collision therefore comes
with a finite product-of-conjugates witness in the free group.  The numerical
SDP solved here is discovery data only.  A positive candidate must still be
rationalized and its recorded reductions replayed by Lean.

For the presentation coboundaries ``d0`` and ``d1`` we form

    Delta1 = d1* d1 + d0 d0*.

The probe searches for ``Delta1 - c I = V* P V`` with ``P >= 0``.  Unlike a
scalar Laplacian radius expansion, the relator-prefix support exposes the
degree-one geometry of the presentation directly.
"""

import argparse
import json
import time

import literal_base_laplacian_sos as literal


ROTATION_TRANSVECTIONS = (
    (-literal.Y, literal.X, literal.Z, -literal.Y, -literal.X),
    (literal.X, literal.Z, -literal.Y, -literal.X, -literal.Y),
    (-literal.Y, literal.X, literal.Y, literal.X, literal.Z),
    (-literal.X, literal.Y, literal.X, literal.Z, -literal.Y),
    (literal.X, -literal.Y, literal.X, literal.Z, -literal.Y, literal.X),
    (-literal.X, literal.Z, -literal.Y, -literal.X, -literal.Y, -literal.X),
)


def p13_relators():
    """The thirteen standard six-transvection relators, after substitution."""
    roots = tuple((i, j) for i in range(3) for j in range(3) if i != j)
    root_index = {root: index for index, root in enumerate(roots)}

    def root_word(root):
        return ROTATION_TRANSVECTIONS[root_index[root]]

    answer = []
    for i in range(3):
        for j in range(3):
            for k in range(3):
                if len({i, j, k}) == 3:
                    answer.append(literal.multiply(
                        literal.commutator(root_word((i, j)),
                                           root_word((j, k))),
                        literal.inverse(root_word((i, k)))))
    for first_index, first in enumerate(roots):
        i, j = first
        for second in roots[first_index + 1:]:
            k, ell = second
            if i != ell and j != k:
                answer.append(literal.commutator(root_word(first),
                                                 root_word(second)))
    block = literal.multiply(
        literal.multiply(root_word((0, 1)),
                         literal.inverse(root_word((1, 0)))),
        root_word((0, 1)))
    answer.append(literal.power(block, 4))
    if len(answer) != 13:
        raise AssertionError("expected the thirteen P13 relators")
    return tuple(answer)


def p13_reduction_status(registry):
    reduced = [registry.reduce(word) for word in p13_relators()]
    return {
        "p13_relators": len(reduced),
        "p13_reduced_to_one": sum(word == () for word in reduced),
        "p13_residual_lengths": [len(word) for word in reduced],
    }


def install_inverse_action_rules():
    """Install certified rules moving inverse translations past rotations."""
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
    def __init__(self):
        super().__init__()
        self._cache = {}
        self._defining_relators = {
            literal.free_reduce(relator.word): (index, False)
            for index, relator in enumerate(literal.RELATORS)
        }
        self._defining_relators.update({
            literal.free_reduce(literal.inverse(relator.word)): (index, True)
            for index, relator in enumerate(literal.RELATORS)
        })

    def reduce(self, word):
        original = literal.free_reduce(word)
        if original in self._cache:
            return self._cache[original]
        if original in self._defining_relators:
            relator_index, inverted = self._defining_relators[original]
            reduced = ()
            atoms = (literal.Atom((), relator_index, inverted),)
        else:
            reduced, atoms = literal.reduce_with_certificate(original)
        self._reductions.setdefault((original, reduced), atoms)
        self._cache[original] = reduced
        return reduced


def add_term(element, group, coefficient):
    if coefficient:
        element[group] = element.get(group, 0) + coefficient
        if element[group] == 0:
            del element[group]


def ring_adjoint(element, registry):
    answer = {}
    for group, coefficient in element.items():
        add_term(answer, registry.reduce(literal.inverse(group)), coefficient)
    return answer


def ring_product(left, right, registry):
    answer = {}
    for first, first_coefficient in left.items():
        for second, second_coefficient in right.items():
            add_term(answer, registry.reduce(first + second),
                     first_coefficient * second_coefficient)
    return answer


def hodge_matrix():
    registry = CachedReductionRegistry()
    generator_words = tuple((letter,) for letter in range(1, 7))
    d0 = []
    for generator in generator_words:
        d0.append({registry.reduce(generator): 1, (): -1})

    prefix_support = {()}
    prefix_support.update(registry.reduce(literal.inverse(generator))
                          for generator in generator_words)
    d1 = []
    for relator_index, relator in enumerate(literal.RELATORS):
        row = [{} for _ in generator_words]
        prefix = ()
        for signed_letter in relator.word:
            generator = abs(signed_letter) - 1
            if signed_letter > 0:
                edge_prefix = prefix
                prefix = registry.reduce(prefix + (signed_letter,))
                coefficient = 1
            else:
                prefix = registry.reduce(prefix + (signed_letter,))
                edge_prefix = prefix
                coefficient = -1
            add_term(row[generator], edge_prefix, coefficient)
            prefix_support.add(edge_prefix)
        if registry.reduce(relator.word) != ():
            raise AssertionError(
                f"defining relator {relator_index} ({relator.name}) "
                "does not have its direct relator certificate")
        d1.append(row)

    size = len(generator_words)
    delta = [[{} for _ in range(size)] for _ in range(size)]
    for left in range(size):
        for right in range(size):
            entry = {}
            for row in d1:
                product = ring_product(
                    ring_adjoint(row[left], registry), row[right], registry)
                for group, coefficient in product.items():
                    add_term(entry, group, coefficient)
            product = ring_product(
                d0[left], ring_adjoint(d0[right], registry), registry)
            for group, coefficient in product.items():
                add_term(entry, group, coefficient)
            delta[left][right] = entry

    for left in range(size):
        for right in range(size):
            if delta[left][right] != ring_adjoint(
                    delta[right][left], registry):
                raise AssertionError("Hodge matrix is not self-adjoint")
    return registry, generator_words, delta, prefix_support


def expanded_support(prefix_support, generator_words, radius, registry):
    support = set(prefix_support)
    frontier = set(prefix_support)
    steps = generator_words + tuple(literal.inverse(generator)
                                    for generator in generator_words)
    for _ in range(radius):
        new_frontier = set()
        for group in frontier:
            for step in steps:
                product = registry.reduce(group + step)
                if product not in support:
                    new_frontier.add(product)
        support.update(new_frontier)
        frontier = new_frontier
    return tuple(sorted(support))


def coefficient_pairs(support, registry):
    pairs = {}
    inverses = [registry.reduce(literal.inverse(group)) for group in support]
    for left, inverse in enumerate(inverses):
        for right, group in enumerate(support):
            product = registry.reduce(inverse + group)
            pairs.setdefault(product, []).append((left, right))
    return pairs


def prepare(radius):
    started = time.time()
    registry, generator_words, delta, prefix_support = hodge_matrix()
    support = expanded_support(
        prefix_support, generator_words, radius, registry)
    pairs = coefficient_pairs(support, registry)
    group_keys = set(pairs)
    for row in delta:
        for entry in row:
            group_keys.update(entry)
    return (started, registry, generator_words, delta, prefix_support,
            support, pairs, tuple(sorted(group_keys)))


def describe(radius, check_p13=False):
    (started, registry, generator_words, delta, prefix_support,
     support, pairs, group_keys) = prepare(radius)
    result = {
        "radius": radius,
        "generators": len(generator_words),
        "relators": len(literal.RELATORS),
        "prefix_support": len(prefix_support),
        "support": len(support),
        "gram_dimension": len(generator_words) * len(support),
        "dense_gram_mebibytes": round(
            (len(generator_words) * len(support)) ** 2 * 8 / 2 ** 20, 3),
        "pair_product_groups": len(pairs),
        "coefficient_classes": len(group_keys),
        "checked_reductions": len(registry.reductions),
        "elapsed_s": round(time.time() - started, 3),
    }
    if check_p13:
        result.update(p13_reduction_status(registry))
    return result


def solve(radius, max_iterations, tolerance, gram_output,
          reduction_output):
    import cvxpy as cp
    import numpy as np

    (started, registry, generator_words, delta, prefix_support,
     support, pairs, group_keys) = prepare(radius)
    block_size = len(support)
    size = len(generator_words)
    dimension = size * block_size
    gram = cp.Variable((dimension, dimension), symmetric=True)
    gap = cp.Variable()
    constraints = [gram >> 0]
    for left in range(size):
        left_offset = left * block_size
        for right in range(size):
            right_offset = right * block_size
            target_entry = delta[left][right]
            for group in group_keys:
                locations = pairs.get(group, ())
                expression = (cp.sum(cp.hstack([
                    gram[left_offset + source, right_offset + target]
                    for source, target in locations
                ])) if locations else 0.0)
                target = float(target_entry.get(group, 0))
                if left == right and group == ():
                    target -= gap
                constraints.append(expression == target)

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
        "radius": radius,
        "generators": len(generator_words),
        "relators": len(literal.RELATORS),
        "prefix_support": len(prefix_support),
        "support": len(support),
        "gram_dimension": dimension,
        "pair_product_groups": len(pairs),
        "coefficient_classes": len(group_keys),
        "checked_reductions": len(registry.reductions),
        "status": problem.status,
        "gap": None if gap.value is None else float(gap.value),
        "constraints": len(constraints),
        "setup_elapsed_s": round(setup_elapsed, 3),
        "total_elapsed_s": round(time.time() - started, 3),
        "solver_iterations": problem.solver_stats.num_iters,
        "solver_time_s": problem.solver_stats.solve_time,
    }
    if gram.value is not None:
        eigenvalues = np.linalg.eigvalsh(0.5 * (gram.value + gram.value.T))
        result.update({
            "gram_min_eigenvalue": float(eigenvalues[0]),
            "gram_max_eigenvalue": float(eigenvalues[-1]),
            "gram_rank_at_1e-7": int(np.sum(eigenvalues > 1e-7)),
            "max_constraint_violation": float(max(
                np.max(np.abs(constraint.violation()))
                for constraint in constraints)),
        })
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=0)
    parser.add_argument("--describe-only", action="store_true")
    parser.add_argument("--check-p13", action="store_true")
    parser.add_argument("--max-iterations", type=int, default=5000)
    parser.add_argument("--tolerance", type=float, default=1e-6)
    parser.add_argument("--gram-output")
    parser.add_argument("--reduction-output")
    args = parser.parse_args()
    if args.check_p13 and not args.describe_only:
        parser.error("--check-p13 is available only with --describe-only")
    result = (describe(args.radius, args.check_p13) if args.describe_only else
              solve(args.radius, args.max_iterations, args.tolerance,
                    args.gram_output, args.reduction_output))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
