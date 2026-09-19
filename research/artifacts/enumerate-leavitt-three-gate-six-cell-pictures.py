#!/usr/bin/env python3
"""Symmetry-reduced census of six-cell universal three-gate pictures."""

from itertools import permutations

TORSION = {"h0", "h2", "k0"}
ORIENTATION = (1, 1, 1, -1, -1, -1)
SIGNS = sum(([1, 1, -1] if sign == 1 else [1, -1, -1]
             for sign in ORIENTATION), [])
POSITIVE = tuple(i for i, sign in enumerate(SIGNS) if sign == 1)
NEGATIVE = tuple(i for i, sign in enumerate(SIGNS) if sign == -1)
ROTATION = tuple(3 * (i // 3) + (i % 3 + 1) % 3 for i in range(18))


def cycles(permutation):
    seen = set()
    result = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        cycle = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = permutation[current]
        result.append(tuple(cycle))
    return tuple(result)


def connected(adjacency):
    reached = {0}
    stack = [0]
    while stack:
        for neighbour in adjacency[stack.pop()]:
            if neighbour not in reached:
                reached.add(neighbour)
                stack.append(neighbour)
    return len(reached) == 6


def reduce_coefficient(word):
    result = []
    for name, sign in word:
        if name in TORSION:
            sign = 1
        if result and result[-1][0] == name and (
                name in TORSION or result[-1][1] == -sign):
            result.pop()
        else:
            result.append((name, sign))
    return tuple(result)


# First enumerate the uncoloured planar cubic ribbon graphs.  Fixing the three
# positive and three negative vertices loses no cases: sign balance forces this
# split, and S_3 x S_3 later reduces relator colours to their two counts.
RIBBONS = []
RAW_GRAPHS = set()
for targets in permutations(NEGATIVE):
    alpha = [None] * 18
    adjacency = [set() for _ in range(6)]
    matrix = [[0] * 6 for _ in range(6)]
    for left, right in zip(POSITIVE, targets):
        alpha[left] = right
        alpha[right] = left
        u, v = left // 3, right // 3
        adjacency[u].add(v)
        adjacency[v].add(u)
        if u == v:
            matrix[u][u] += 1
        else:
            matrix[u][v] += 1
            matrix[v][u] += 1
    if not connected(adjacency):
        continue
    regions = cycles(tuple(ROTATION[alpha[i]] for i in range(18)))
    if len(regions) != 5:  # 6-9+F=2
        continue
    RIBBONS.append((tuple(alpha), regions))
    RAW_GRAPHS.add(tuple(sum(matrix, [])))


# There are sixteen underlying connected planar cubic multigraph types.  The
# unique loopless, parallel-free one is the triangular prism; the other types
# are its loop/parallel-edge (theta and K4-derived) degenerations.
VERTEX_PERMUTATIONS = tuple(permutations(range(6)))


def canonical_graph(flat):
    matrix = [flat[6 * i:6 * i + 6] for i in range(6)]
    return min(tuple(matrix[p[i]][p[j]]
                     for i in range(6) for j in range(i, 6))
               for p in VERTEX_PERMUTATIONS)


GRAPH_TYPES = {canonical_graph(flat) for flat in RAW_GRAPHS}
assert len(GRAPH_TYPES) == 16


def corners(relator, orientation):
    positive = (("k1", 1), ("k2", 1), ("k0", 1)) if relator else (
        ("h1", 1), ("h2", 1), ("h0", 1))
    if orientation == 1:
        return positive
    return ((positive[1][0], -1),
            (positive[0][0], -1),
            (positive[2][0], -1))


checked = 0
candidate_disks = 0
needed_relations = set()

# The counts of R1 vertices among the three vertices of each orientation are
# complete orbit representatives for the S_3 x S_3 action: 4 x 4 cases.
for positive_r1_count in range(4):
    for negative_r1_count in range(4):
        relators = tuple(
            [1 if i < positive_r1_count else 0 for i in range(3)]
            + [1 if i < negative_r1_count else 0 for i in range(3)]
        )
        vertex_corners = tuple(corners(relators[v], ORIENTATION[v])
                               for v in range(6))

        for alpha, regions in RIBBONS:
            # Occurrence i of R and occurrence 2-i of R^-1 form an immediate
            # dipole if an arc joins them.
            if any(relators[left // 3] == relators[alpha[left] // 3]
                   and ORIENTATION[left // 3] == -ORIENTATION[alpha[left] // 3]
                   and left % 3 + alpha[left] % 3 == 2
                   for left in POSITIVE):
                continue
            checked += 1

            labels = []
            for region in regions:
                label = [
                    vertex_corners[alpha[half] // 3][alpha[half] % 3]
                    for half in region
                ]
                labels.append(reduce_coefficient(label))
            trivial_regions = sum(not label for label in labels)
            if trivial_regions >= 4:  # choose the fifth as the outer region
                candidate_disks += 1
            elif trivial_regions == 3:
                # Either nontrivial region can be outer.  The other is exactly
                # the additional coefficient identity needed to close this
                # otherwise square-only six-cell picture.
                needed_relations.update(label for label in labels if label)

assert checked == 596856
assert candidate_disks == 0
minimum_needed_length = min(map(len, needed_relations))
shortest_needed_relations = {
    relation for relation in needed_relations
    if len(relation) == minimum_needed_length
}
from collections import Counter
print("DEBUG needed", len(needed_relations), Counter(map(len, needed_relations)))
print("DEBUG shortest", minimum_needed_length, sorted(shortest_needed_relations))
print("PASS: 16 cubic planar multigraph types and 596856 reduced colourings")
print("      contain no six-cell universal three-gate boundary picture")
