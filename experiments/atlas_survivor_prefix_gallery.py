"""Search exact sequential scalar-chart galleries for atlas survivors.

A one-chart certificate asks one scalar leaf chart to contain every letter of
a relator.  This script uses a weaker, genuinely multi-chart certificate.
For a cyclic word ``l_1 ... l_m = 1``, put ``q_i=l_1 ... l_i``.  At step
``i`` we allow a new scalar chart containing both ``q_i`` and ``l_(i+1)``.
The old and new lifts of ``q_i`` are compared in a common refinement; the
transition is accepted only when ``q_i`` lies in the derived subgroup of
the relevant overlap blocks.  The original lift of the next letter is
checked in the same way.  A closed gallery is therefore a rigorous proof
that the relator is trivial in the universal central atlas cover.

All Leavitt arithmetic and all linear algebra are exact over F_2.  Failure
within the requested leaf bound is only a bounded-search result.
"""

import argparse
import json
import sys

import numpy as np

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import (  # noqa: E402
    ONE,
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_perfect_overlap_scan import (  # noqa: E402
    CHART_LEAVES,
    cardinality_obstruction,
    refinement_levels,
    suffix_codes,
)
from atlas_survivor_conjugacy import (  # noqa: E402
    cyclic_reduce,
    invert_word,
    unoriented_key,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    leavitt_chart_element,
    leavitt_is_one,
    leavitt_mul,
    matrix_key,
)


def value_key(value):
    return tuple(sorted(term for term, coefficient in value.items()
                        if coefficient & 1))


def expand_terms(value, depths):
    """Expand a Leavitt value to fixed right depths in each gauge degree."""
    answer = set()
    for (left, right), coefficient in value.items():
        if not coefficient & 1:
            continue
        degree = len(left) - len(right)
        extra = depths[degree] - len(right)
        for bits in range(1 << extra):
            suffix = tuple((bits >> index) & 1 for index in range(extra))
            term = (left + suffix, right + suffix)
            if term in answer:
                answer.remove(term)
            else:
                answer.add(term)
    return answer


def chart_matrix(value, code):
    """Return the matrix of ``value`` in a scalar chart, or ``None``.

    The matrix units ``alpha beta*`` for ``alpha,beta`` in a complete prefix
    code are expanded together with ``value`` to common homogeneous right
    depths.  Exact Gaussian elimination over F_2 then tests membership in
    their span and recovers the unique coefficient matrix.
    """
    words = [tuple(int(bit) for bit in leaf) for leaf in code]
    basis_values = [
        {(left, right): 1}
        for left in words for right in words
    ]
    depths = {}
    for current in [value, *basis_values]:
        for left, right in current:
            degree = len(left) - len(right)
            depths[degree] = max(depths.get(degree, 0), len(right))

    expanded = [expand_terms(current, depths)
                for current in [value, *basis_values]]
    universe = {term for terms in expanded for term in terms}
    indices = {term: index for index, term in enumerate(sorted(universe))}

    def encode(terms):
        result = 0
        for term in terms:
            result ^= 1 << indices[term]
        return result

    pivots = {}
    for column, terms in enumerate(expanded[1:]):
        vector = encode(terms)
        combination = 1 << column
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (vector, combination)
                break
            old_vector, old_combination = pivots[pivot]
            vector ^= old_vector
            combination ^= old_combination
        if not vector:
            raise AssertionError("scalar chart matrix units became dependent")

    target = encode(expanded[0])
    combination = 0
    while target:
        pivot = target.bit_length() - 1
        if pivot not in pivots:
            return None
        vector, coefficients = pivots[pivot]
        target ^= vector
        combination ^= coefficients

    size = len(code)
    matrix = np.zeros((size, size), dtype=np.uint8)
    for index in range(size * size):
        if (combination >> index) & 1:
            matrix[index // size, index % size] = 1
    return matrix


def common_refinement(first, second):
    """Least common refinement of two complete binary prefix codes."""
    leaves = set()
    for left in first:
        for right in second:
            if left.startswith(right):
                leaves.add(left)
            elif right.startswith(left):
                leaves.add(right)
    return tuple(sorted(leaves))


def support_components(matrix):
    unseen = set(range(len(matrix)))
    components = []
    while unseen:
        seed = unseen.pop()
        component = {seed}
        frontier = [seed]
        while frontier:
            current = frontier.pop()
            neighbors = {
                index for index in range(len(matrix))
                if matrix[current, index] or matrix[index, current]
            }
            for neighbor in neighbors.difference(component):
                component.add(neighbor)
                unseen.discard(neighbor)
                frontier.append(neighbor)
        components.append(tuple(sorted(component)))
    return components


def derived_bridge(matrix, suffixes):
    """Test membership in the derived subgroup of a refinement overlap."""
    for row in range(len(matrix)):
        for column in range(len(matrix)):
            if matrix[row, column] and suffixes[row] != suffixes[column]:
                return False
    for component in support_components(matrix):
        if len(component) == 1:
            continue
        multiplicity = len(suffixes[component[0]])
        dimension = len(component) * multiplicity
        if dimension >= 3:
            continue
        block = matrix[np.ix_(component, component)]
        identity = np.eye(2, dtype=np.uint8)
        if not np.array_equal((block @ block @ block) & 1, identity):
            return False
    return True


def bridge_between_representations(first, second, matrices):
    """Certify that two scalar-chart lifts of ``value`` agree."""
    refinement = common_refinement(first, second)
    first_suffixes = suffix_codes(refinement, first)
    second_suffixes = suffix_codes(refinement, second)
    return (
        (first == refinement
         or derived_bridge(matrices[first], first_suffixes))
        and (second == refinement
             or derived_bridge(matrices[second], second_suffixes))
    )


def letter_bridge(factor, matrix, target_code, target_matrix):
    """Compare an original A8-letter lift with its target-chart lift."""
    source = CHART_LEAVES[factor]
    refinement = common_refinement(source, target_code)
    source_suffixes = suffix_codes(refinement, source)
    if chart_matrix(leavitt_chart_element(factor, matrix), target_code) is None:
        raise AssertionError("target chart lost the represented letter")
    if target_matrix.shape != (len(target_code), len(target_code)):
        raise AssertionError("target matrix has the wrong size")
    return derived_bridge(matrix, source_suffixes)


def survivor_representatives():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity
        for projection in factor_projections(word))]
    classes = {}
    for index, word in enumerate(boundary):
        obstruction = cardinality_obstruction(word)
        if obstruction["positive_cardinality_obstruction_rows"]:
            classes.setdefault(unoriented_key(word), (index, cyclic_reduce(word)))
    if [entry[0] for entry in classes.values()] != [11, 30, 44, 55]:
        raise AssertionError("survivor classification changed")
    return list(classes.values())[:2]


def oriented_rotations(word):
    answer = []
    for inverted, oriented in ((False, word), (True, invert_word(word))):
        for offset in range(len(oriented)):
            answer.append((
                inverted,
                offset,
                oriented[offset:] + oriented[:offset],
            ))
    return answer


def search_word(word, codes):
    prefixes = [ONE]
    for factor, matrix in word:
        prefixes.append(leavitt_mul(
            prefixes[-1], leavitt_chart_element(factor, matrix)))
    if not leavitt_is_one(prefixes[-1]):
        raise AssertionError("survivor is not a Leavitt relation")

    values = {value_key(value): value for value in prefixes}
    for factor, matrix in word:
        letter = leavitt_chart_element(factor, matrix)
        values.setdefault(value_key(letter), letter)

    representations = {}
    for key, value in values.items():
        representations[key] = {
            code: matrix
            for code in codes
            if (matrix := chart_matrix(value, code)) is not None
        }

    frontier = {}
    parents = []
    frontier_codes = []
    for step, (factor, letter_matrix) in enumerate(word):
        prefix = prefixes[step]
        following_prefix = prefixes[step + 1]
        prefix_reps = representations[value_key(prefix)]
        following_reps = representations[value_key(following_prefix)]
        letter_value = leavitt_chart_element(factor, letter_matrix)
        letter_reps = representations[value_key(letter_value)]
        following = {}
        parent_layer = {}
        for code in codes:
            if code not in prefix_reps or code not in letter_reps:
                continue
            if code not in following_reps:
                raise AssertionError("chart membership is not multiplicative")
            if not letter_bridge(
                    factor, letter_matrix, code, letter_reps[code]):
                continue
            if step == 0:
                following[code] = True
                parent_layer[code] = None
                continue
            for old_code in frontier:
                if bridge_between_representations(
                        old_code, code, prefix_reps):
                    following[code] = True
                    parent_layer[code] = old_code
                    break
        parents.append(parent_layer)
        frontier = following
        frontier_codes.append([list(code) for code in frontier])
        if not frontier:
            return None, {
                "failed_step": step + 1,
                "prefix_chart_counts": [len(layer) for layer in parents],
                "prefix_charts": frontier_codes,
            }

    final_code = next(iter(frontier))
    gallery = [final_code]
    for layer in reversed(parents[1:]):
        gallery.append(layer[gallery[-1]])
    gallery.reverse()
    return gallery, {
        "prefix_chart_counts": [len(layer) for layer in parents],
        "prefix_charts": frontier_codes,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-leaves", type=int, default=9)
    args = parser.parse_args()
    if args.max_leaves < 5:
        raise ValueError("all searched scalar charts must be superperfect")

    codes = []
    level_counts = {}
    for leaf_count, level in refinement_levels(args.max_leaves):
        level_counts[str(leaf_count)] = len(level)
        codes.extend(level)

    results = []
    for boundary_index, representative in survivor_representatives():
        attempts = []
        found = None
        for inverted, rotation, word in oriented_rotations(representative):
            gallery, diagnostics = search_word(word, codes)
            attempts.append({
                "inverted": inverted,
                "rotation": rotation,
                **diagnostics,
            })
            if gallery is not None:
                found = {
                    "inverted": inverted,
                    "rotation": rotation,
                    "gallery": [list(code) for code in gallery],
                }
                break
        results.append({
            "boundary_index": boundary_index,
            "certificate": found,
            "attempts": attempts,
        })

    print(json.dumps({
        "max_leaves": args.max_leaves,
        "level_counts": level_counts,
        "candidate_charts": len(codes),
        "results": results,
    }, indent=2))


if __name__ == "__main__":
    main()
