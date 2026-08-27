#!/usr/bin/env python3
"""Enumerate universal three-gate relative pictures of area two and four.

The coefficient model retains exactly h0^2=h2^2=k0^2=1 and otherwise makes
the six corner labels free.  Relator vertices are trivalent ribbon vertices;
z-arcs pair opposite signs.  A planar connected pairing is a candidate disk
when all but at most one coefficient region have trivial label.
"""

from itertools import permutations, product

TORSION = {"h0", "h2", "k0"}
CORNERS = {
    0: (("h1", 1), ("h2", 1), ("h0", 1)),
    1: (("k1", 1), ("k2", 1), ("k0", 1)),
}


def vertex(relator, orientation):
    corners = CORNERS[relator]
    if orientation == 1:
        return ((1, corners[0]), (1, corners[1]), (-1, corners[2]))
    # Cyclic form of the inverse: z g2^-1 z^-1 g1^-1 z^-1 g0^-1.
    return ((1, (corners[1][0], -1)),
            (-1, (corners[0][0], -1)),
            (-1, (corners[2][0], -1)))


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
        result.append(cycle)
    return result


def census(area):
    planar_reduced = 0
    candidate_disks = 0
    for orientations in product((1, -1), repeat=area):
        # Three legs per vertex; sign balance forces equal orientations.
        if sum(orientations):
            continue
        for relators in product((0, 1), repeat=area):
            vertices = [vertex(relators[v], orientations[v])
                        for v in range(area)]
            halves = [(v, i) for v in range(area) for i in range(3)]
            index = {half: i for i, half in enumerate(halves)}
            positive = [half for half in halves
                        if vertices[half[0]][half[1]][0] == 1]
            negative = [half for half in halves
                        if vertices[half[0]][half[1]][0] == -1]

            for targets in permutations(negative):
                pairs = tuple(zip(positive, targets))

                # In the chosen cyclic coordinates, occurrence i of R and
                # occurrence 2-i of R^-1 are inverse occurrences.  An arc
                # joining such a pair is a picture dipole and is excluded.
                if any(relators[left[0]] == relators[right[0]]
                       and orientations[left[0]] == -orientations[right[0]]
                       and left[1] + right[1] == 2
                       for left, right in pairs):
                    continue

                adjacency = [set() for _ in range(area)]
                alpha = [None] * (3 * area)
                for left, right in pairs:
                    adjacency[left[0]].add(right[0])
                    adjacency[right[0]].add(left[0])
                    alpha[index[left]] = index[right]
                    alpha[index[right]] = index[left]

                reached = {0}
                stack = [0]
                while stack:
                    for neighbour in adjacency[stack.pop()]:
                        if neighbour not in reached:
                            reached.add(neighbour)
                            stack.append(neighbour)
                if len(reached) != area:
                    continue

                rotation = [index[(v, (i + 1) % 3)]
                            for v in range(area) for i in range(3)]
                regions = cycles([rotation[alpha[i]]
                                  for i in range(3 * area)])

                # Euler on the sphere: V-E+F=2, with E=3V/2.
                if len(regions) != 2 + area // 2:
                    continue
                planar_reduced += 1

                labels = []
                for region in regions:
                    labels.append(reduce_coefficient([
                        vertices[halves[alpha[half]][0]]
                                [halves[alpha[half]][1]][1]
                        for half in region
                    ]))
                if sum(not label for label in labels) >= len(labels) - 1:
                    candidate_disks += 1

    return planar_reduced, candidate_disks


assert census(2)[1] == 0
assert census(4)[1] == 0
print("PASS: no reduced universal three-gate coefficient-boundary picture")
print("      exists with two or four relator vertices")

