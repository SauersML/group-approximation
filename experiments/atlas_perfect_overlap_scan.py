"""Find atlas kernel words killed by finite perfect-overlap bridges.

Let C1 and C2 be the two four-leaf charts used by the binary Leavitt atlas.
A kernel word dies in the universal central cover if all of its letters can
be transported into one superperfect scalar chart and every transport is
forced across a perfect overlap.  This script searches common refinements of
C1 and C2 and checks that sufficient condition exactly over F_2.

The scan is deliberately one-sided.  A reported certificate is a proof that
the word lies in [P,R].  A survivor need not be nonzero in R/[P,R]; it only
survives this bounded family of perfect-overlap certificates.
"""

import argparse
import collections
import json

import numpy as np

from atlas_kernel_collision_enumerator import (
    encode_word,
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import CHART_LEAVES, I4, gf2_mul, matrix_key


COMMON_REFINEMENT = ("000", "001", "010", "011", "1")
SUFFIX_VARIABLES = ("A", "B", "C", "D", "E", "F", "G")
FACTOR_VARIABLES = {
    1: (0, 1, 2, 3),       # (A,B,C,D)
    2: (4, 1, 5, 6),       # (E,B,F,G)
}


def refinement_levels(max_leaves):
    """Enumerate all refinements of the least common chart refinement."""
    level = {tuple(sorted(COMMON_REFINEMENT))}
    yield len(COMMON_REFINEMENT), tuple(sorted(level))
    for leaf_count in range(len(COMMON_REFINEMENT) + 1, max_leaves + 1):
        following = set()
        for code in level:
            for index, leaf in enumerate(code):
                refined = list(code)
                refined[index:index + 1] = (leaf + "0", leaf + "1")
                following.add(tuple(sorted(refined)))
        level = following
        yield leaf_count, tuple(sorted(level))


def suffix_codes(code, chart):
    """Return the descendant suffix code below every leaf of chart."""
    answer = []
    for source in chart:
        descendants = tuple(sorted(
            leaf[len(source):] for leaf in code if leaf.startswith(source)))
        if not descendants:
            return None
        answer.append(descendants)
    if sum(len(value) for value in answer) != len(code):
        return None
    return tuple(answer)


def support_components(matrix):
    """Connected blocks of the row/column support graph of a matrix."""
    unseen = set(range(4))
    components = []
    while unseen:
        seed = unseen.pop()
        component = {seed}
        frontier = [seed]
        while frontier:
            current = frontier.pop()
            neighbors = {
                index for index in range(4)
                if matrix[current, index] or matrix[index, current]
            }
            for neighbor in neighbors.difference(component):
                component.add(neighbor)
                unseen.discard(neighbor)
                frontier.append(neighbor)
        components.append(tuple(sorted(component)))
    return tuple(components)


def block_is_in_derived_group(matrix, component, multiplicity):
    """Test the only nonperfect case GL_2(F_2); larger GL blocks are perfect."""
    dimension = len(component) * multiplicity
    if dimension >= 3:
        return True
    if dimension == 1:
        return True
    block = matrix[np.ix_(component, component)]
    identity = np.eye(2, dtype=np.uint8)
    # [GL_2(2),GL_2(2)] is its order-three subgroup A_3.
    return np.array_equal(gf2_mul(gf2_mul(block, block), block), identity)


def bridge_certifies(matrix, suffixes):
    """Certify one chart letter through uniform-refinement perfect overlaps."""
    if not represented_on_code(matrix, suffixes):
        return False
    for component in support_components(matrix):
        if len(component) == 1:
            continue
        multiplicity = len(suffixes[component[0]])
        if not block_is_in_derived_group(matrix, component, multiplicity):
            return False
    return True


def represented_on_code(matrix, suffixes):
    """Test whether prefix refinement puts a chart matrix on this code."""
    for row in range(4):
        for col in range(4):
            if matrix[row, col] and suffixes[row] != suffixes[col]:
                return False
    return True


def embedded_matrix(matrix, chart, suffixes, code):
    """Evaluate a represented chart matrix on the candidate common code."""
    indices = {leaf: index for index, leaf in enumerate(code)}
    value = np.zeros((len(code), len(code)), dtype=np.uint8)
    for row in range(4):
        for col in range(4):
            if not matrix[row, col]:
                continue
            if suffixes[row] != suffixes[col]:
                raise AssertionError("matrix is not represented on this code")
            for suffix in suffixes[row]:
                value[indices[chart[row] + suffix],
                      indices[chart[col] + suffix]] ^= 1
    return value


def classify_word(word, candidates):
    first_common_chart = None
    for leaf_count, code, suffixes_by_factor in candidates:
        represented = []
        bridge_valid = True
        for factor, matrix in word:
            suffixes = suffixes_by_factor[factor]
            if not represented_on_code(matrix, suffixes):
                represented = None
                break
            bridge_valid = bridge_valid and bridge_certifies(matrix, suffixes)
            represented.append(embedded_matrix(
                matrix, CHART_LEAVES[factor], suffixes, code))
        if represented is None:
            continue
        product = np.eye(leaf_count, dtype=np.uint8)
        for matrix in represented:
            product = (product @ matrix) & 1
        if not np.array_equal(product, np.eye(leaf_count, dtype=np.uint8)):
            raise AssertionError("common-chart image of a kernel word is nontrivial")
        if first_common_chart is None:
            first_common_chart = (leaf_count, code)
        if bridge_valid:
            return (leaf_count, code), first_common_chart
    return None, first_common_chart


def cardinality_obstruction(word):
    """Return an exact positive-cardinality obstruction to any common chart.

    If a common refinement exists, write its suffix codes under the first
    chart as A,B,C,D and under the second as E,B,F,G.  The binary tree gives

        |A|=|F|+|G|,   |E|=|C|+|D|.

    Matrix support identifies some variables.  After those identifications,
    a row whose nonzero coefficients have only one sign cannot vanish on
    positive suffix-code cardinalities.
    """
    parent = list(range(len(SUFFIX_VARIABLES)))

    def find(value):
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    def union(left, right):
        left = find(left)
        right = find(right)
        if left != right:
            parent[right] = left

    for factor, matrix in word:
        variables = FACTOR_VARIABLES[factor]
        for row in range(4):
            for col in range(4):
                if matrix[row, col]:
                    union(variables[row], variables[col])

    equations = []
    for terms in (
            ((0, 1), (5, -1), (6, -1)),
            ((4, 1), (2, -1), (3, -1))):
        coefficients = collections.defaultdict(int)
        for variable, coefficient in terms:
            coefficients[find(variable)] += coefficient
        equations.append({root: coefficient for root, coefficient
                          in coefficients.items() if coefficient})

    roots = sorted({find(variable) for variable in range(len(parent))})
    classes = {
        root: [SUFFIX_VARIABLES[variable]
               for variable in range(len(parent)) if find(variable) == root]
        for root in roots
    }
    encoded_equations = []
    obstructing_rows = []
    for row, equation in enumerate(equations):
        encoded = [
            {"class": classes[root], "coefficient": equation.get(root, 0)}
            for root in roots if equation.get(root, 0)
        ]
        encoded_equations.append(encoded)
        signs = [entry["coefficient"] for entry in encoded]
        if signs and (all(value > 0 for value in signs)
                      or all(value < 0 for value in signs)):
            obstructing_rows.append(row)
    return {
        "classes": list(classes.values()),
        "cardinality_equations": encoded_equations,
        "positive_cardinality_obstruction_rows": obstructing_rows,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=5)
    parser.add_argument("--max-leaves", type=int, default=12)
    parser.add_argument("--boundary-only", action="store_true")
    parser.add_argument("--output")
    parser.add_argument("--summary-only", action="store_true")
    args = parser.parse_args()
    if args.radius < 0 or args.max_leaves < len(COMMON_REFINEMENT):
        raise ValueError("invalid radius or leaf bound")

    candidates = []
    candidate_counts = {}
    for leaf_count, codes in refinement_levels(args.max_leaves):
        candidate_counts[str(leaf_count)] = len(codes)
        for code in codes:
            suffixes = {
                factor: suffix_codes(code, CHART_LEAVES[factor])
                for factor in (1, 2)
            }
            if all(value is not None for value in suffixes.values()):
                candidates.append((leaf_count, code, suffixes))

    states, level_sizes = enumerate_ball(args.radius)
    words, _, _ = spanning_tree_kernel_words(states)
    if args.boundary_only:
        identity_key = matrix_key(I4)
        words = [word for word in words if any(
            matrix_key(projection) != identity_key
            for projection in factor_projections(word))]

    certificates = []
    survivors = []
    histogram = {}
    common_chart_survivors = 0
    cardinality_obstructions = 0
    projection_classes = collections.Counter()
    for index, word in enumerate(words):
        certificate, common_chart = classify_word(word, candidates)
        if certificate is None:
            projections = factor_projections(word)
            projection_pair = tuple(
                matrix_key(projection).hex() for projection in projections)
            projection_classes[projection_pair] += 1
            if common_chart is not None:
                common_chart_survivors += 1
            obstruction = cardinality_obstruction(word)
            if obstruction["positive_cardinality_obstruction_rows"]:
                cardinality_obstructions += 1
            survivors.append({
                "word_index": index,
                "length": len(word),
                "projection_pair": list(projection_pair),
                "common_chart_leaf_count": (
                    common_chart[0] if common_chart is not None else None),
                "common_chart_code": (
                    list(common_chart[1]) if common_chart is not None else None),
                "cardinality_analysis": obstruction,
                "word": encode_word(word),
            })
            continue
        leaf_count, code = certificate
        histogram[str(leaf_count)] = histogram.get(str(leaf_count), 0) + 1
        certificates.append({
            "word_index": index,
            "length": len(word),
            "leaf_count": leaf_count,
            "code": list(code),
        })

    result = {
        "radius": args.radius,
        "sphere_sizes": level_sizes,
        "boundary_only": args.boundary_only,
        "max_leaves": args.max_leaves,
        "candidate_counts": candidate_counts,
        "tested_words": len(words),
        "perfect_overlap_certificates": len(certificates),
        "survivors": len(survivors),
        "survivors_with_common_chart": common_chart_survivors,
        "survivors_with_global_cardinality_obstruction": (
            cardinality_obstructions),
        "survivor_projection_classes": [
            {"projection_pair": list(pair), "multiplicity": multiplicity}
            for pair, multiplicity in sorted(projection_classes.items())
        ],
        "minimum_leaf_histogram": histogram,
        "certificate_records": certificates,
        "survivor_records": survivors,
    }
    encoded = json.dumps(result, indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(encoded + "\n")
    if args.summary_only:
        summary = dict(result)
        summary.pop("certificate_records")
        summary.pop("survivor_records")
        print(json.dumps(summary, indent=2))
    else:
        print(encoded)


if __name__ == "__main__":
    main()
