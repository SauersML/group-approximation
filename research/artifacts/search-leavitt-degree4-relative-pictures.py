#!/usr/bin/env python3
"""Search exact low-area relative pictures for the revised degree-four word.

The coefficient group is the free product of four copies of
EL_20(L_F2(1,2)).  Equality inside each copy is decided in the faithful
twenty-leaf Bergman chart, not in a finite quotient.  The four cyclic-cover
relators have valences 1,3,3,1 in the stable letter z.  We enumerate connected
planar signed ribbon pairings and ask whether all but one coefficient regions
are trivial, with the remaining region equal (up to a corner rotation) to
[c_0,p_0^2 c_0 p_0^-2].
"""

import argparse
from functools import lru_cache
from itertools import combinations_with_replacement, permutations


def xor(*sets):
    out = set()
    for values in sets:
        out.symmetric_difference_update(values)
    return out


def canon(terms):
    def monomial(u, v):
        if u and v and u[-1] == "1" and v[-1] == "1":
            return xor(monomial(u[:-1], v[:-1]),
                       monomial(u[:-1] + "0", v[:-1] + "0"))
        return {(u, v)}

    out = set()
    for u, v in terms:
        out.symmetric_difference_update(monomial(u, v))
    return frozenset(out)


def mul_monomial(left, right):
    u, v = left
    x, y = right
    if x.startswith(v):
        return u + x[len(v):], y
    if v.startswith(x):
        return u, y + v[len(x):]
    return None


@lru_cache(maxsize=None)
def mul(left, right):
    out = set()
    for first in left:
        for second in right:
            term = mul_monomial(first, second)
            if term is not None:
                if term in out:
                    out.remove(term)
                else:
                    out.add(term)
    return canon(out)


ONE = canon({("", "")})
S0 = canon({("0", "")})
S1 = canon({("1", "")})
T0 = canon({("", "0")})
T1 = canon({("", "1")})


def prefix(index):
    return "1" * (index - 1) + "0" if index < 20 else "1" * 19


def root(row, coefficient, column):
    out = set(ONE)
    for u, v in coefficient:
        out.symmetric_difference_update(canon({
            (prefix(row) + u, prefix(column) + v)
        }))
    return canon(out)


def power(unit, exponent):
    result = ONE
    for _ in range(exponent):
        result = mul(result, unit)
    return result


def cycle():
    return canon({(prefix(index % 20 + 1), prefix(index))
                  for index in range(1, 21)})


A = root(1, S0, 2)
E = root(1, T1, 2)
Q = mul(root(3, S1, 4), root(11, T0, 12))
P = cycle()
PINV = power(P, 19)
R = mul(Q, P)
RINV = mul(PINV, Q)
C = root(1, S0, 3)
B = mul(mul(mul(mul(R, R), A), RINV), RINV)
D = mul(mul(mul(mul(P, P), C), PINV), PINV)

UNITS = {"a": A, "e": E, "p": P, "r": R, "c": C, "b": B, "d": D}
INVERSES = {"a": A, "e": E, "p": PINV, "r": RINV,
            "c": C, "b": B, "d": D}
TARGET = mul(mul(mul(C, D), C), D)
TARGET_INV = mul(mul(mul(D, C), D), C)
assert TARGET != ONE


# Tokens are ("z", sign) or ("g", copy, name, exponent).
RELATORS = (
    (("g", 0, "r", 1), ("g", 1, "e", 1), ("g", 2, "a", 1),
     ("g", 1, "c", 1), ("g", 3, "b", 1), ("g", 2, "d", 1),
     ("g", 3, "p", 1), ("z", 1)),
    (("g", 1, "r", 1), ("g", 2, "e", 1), ("g", 3, "a", 1),
     ("g", 2, "c", 1), ("z", 1), ("g", 0, "b", 1),
     ("z", -1), ("g", 3, "d", 1), ("z", 1),
     ("g", 0, "p", 1)),
    (("g", 2, "r", 1), ("g", 3, "e", 1), ("z", 1),
     ("g", 0, "a", 1), ("z", -1), ("g", 3, "c", 1),
     ("z", 1), ("g", 1, "b", 1), ("g", 0, "d", 1),
     ("g", 1, "p", 1)),
    (("g", 3, "r", 1), ("z", 1), ("g", 0, "e", 1),
     ("g", 1, "a", 1), ("g", 0, "c", 1), ("g", 2, "b", 1),
     ("g", 1, "d", 1), ("g", 2, "p", 1)),
)


def inverse_tokens(word):
    result = []
    for token in reversed(word):
        if token[0] == "z":
            result.append(("z", -token[1]))
        else:
            result.append(("g", token[1], token[2], -token[3]))
    return tuple(result)


def vertex(relator, orientation):
    word = RELATORS[relator] if orientation == 1 else inverse_tokens(
        RELATORS[relator])
    first = next(index for index, token in enumerate(word) if token[0] == "z")
    word = word[first:] + word[:first]
    signs = []
    corners = []
    index = 0
    while index < len(word):
        assert word[index][0] == "z"
        signs.append(word[index][1])
        index += 1
        corner = []
        while index < len(word) and word[index][0] != "z":
            corner.append(word[index][1:])
            index += 1
        corners.append(tuple(corner))
    return tuple(signs), tuple(corners)


VERTEX_TYPES = tuple((relator, orientation, *vertex(relator, orientation))
                     for relator in range(4) for orientation in (1, -1))


@lru_cache(maxsize=None)
def evaluate_block(letters):
    result = ONE
    for name, exponent in letters:
        result = mul(result, UNITS[name] if exponent == 1 else INVERSES[name])
    return result


@lru_cache(maxsize=None)
def reduce_free_product(factors):
    stack = []
    for copy, name, exponent in factors:
        unit = UNITS[name] if exponent == 1 else INVERSES[name]
        if unit == ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = mul(stack.pop()[1], unit)
            if unit == ONE:
                continue
        stack.append((copy, unit))
    # Removing an identity block can expose equal-copy neighbours.
    changed = True
    while changed:
        changed = False
        out = []
        for copy, unit in stack:
            if out and out[-1][0] == copy:
                unit = mul(out.pop()[1], unit)
                changed = True
                if unit == ONE:
                    continue
            out.append((copy, unit))
        stack = out
    return tuple(stack)


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


def target_rotation(corners):
    factors = tuple(factor for corner in corners for factor in corner)
    for offset in range(len(factors) or 1):
        rotated = factors[offset:] + factors[:offset]
        reduced = reduce_free_product(rotated)
        if len(reduced) == 1 and reduced[0][0] == 0 and reduced[0][1] in (
                TARGET, TARGET_INV):
            return offset
    return None


def connected(vertex_count, pairs):
    adjacency = [set() for _ in range(vertex_count)]
    for left, right in pairs:
        adjacency[left[0]].add(right[0])
        adjacency[right[0]].add(left[0])
    reached = {0}
    stack = [0]
    while stack:
        for neighbour in adjacency[stack.pop()]:
            if neighbour not in reached:
                reached.add(neighbour)
                stack.append(neighbour)
    return len(reached) == vertex_count


def census(area, stop_on_hit=False, shard=0, shards=1):
    planar = 0
    exact_disks = 0
    one_copy_disks = 0
    one_copy_units = set()
    type_multisets = 0
    for choice_index, choices in enumerate(combinations_with_replacement(
            range(len(VERTEX_TYPES)), area)):
        if choice_index % shards != shard:
            continue
        vertices = [VERTEX_TYPES[choice] for choice in choices]
        halves = [(v, leg) for v, vertex_data in enumerate(vertices)
                  for leg in range(len(vertex_data[2]))]
        if len(halves) % 2:
            continue
        positive = [half for half in halves
                    if vertices[half[0]][2][half[1]] == 1]
        negative = [half for half in halves
                    if vertices[half[0]][2][half[1]] == -1]
        if len(positive) != len(negative):
            continue
        type_multisets += 1
        index = {half: position for position, half in enumerate(halves)}
        rotation = [None] * len(halves)
        for v, vertex_data in enumerate(vertices):
            valence = len(vertex_data[2])
            for leg in range(valence):
                rotation[index[(v, leg)]] = index[(v, (leg + 1) % valence)]

        for targets in permutations(negative):
            pairs = tuple(zip(positive, targets))
            if not connected(area, pairs):
                continue
            alpha = [None] * len(halves)
            for left, right in pairs:
                alpha[index[left]] = index[right]
                alpha[index[right]] = index[left]
            regions = cycles(tuple(rotation[alpha[i]] for i in range(len(halves))))
            edges = len(halves) // 2
            if len(regions) != 2 - area + edges:
                continue
            planar += 1

            region_corners = []
            trivial = []
            targets_found = []
            reduced_regions = []
            for region in regions:
                corners = tuple(
                    vertices[halves[alpha[half]][0]][3][halves[alpha[half]][1]]
                    for half in region)
                region_corners.append(corners)
                factors = tuple(factor for corner in corners for factor in corner)
                reduced = reduce_free_product(factors)
                reduced_regions.append(reduced)
                trivial.append(not reduced)
                targets_found.append(target_rotation(corners))
            for outer, reduced in enumerate(reduced_regions):
                if (len(reduced) == 1 and all(
                        trivial[index] for index in range(len(regions))
                        if index != outer)):
                    one_copy_disks += 1
                    one_copy_units.add((reduced[0][0], reduced[0][1]))
                    if one_copy_disks <= 5:
                        print("ONE_COPY_BOUNDARY", flush=True)
                        print("area", area, "choices", choices, flush=True)
                        print("vertex_types", [(v[0], v[1]) for v in vertices],
                              flush=True)
                        print("pairs", pairs, flush=True)
                        print("regions", regions, "outer", outer, flush=True)
                        print("outer_corners", region_corners[outer], flush=True)
                        print("copy", reduced[0][0], "bergman_terms",
                              len(reduced[0][1]), flush=True)
            for outer, target_offset in enumerate(targets_found):
                if target_offset is not None and all(
                        trivial[index] for index in range(len(regions))
                        if index != outer):
                    exact_disks += 1
                    print("FOUND", flush=True)
                    print("area", area, "choices", choices, flush=True)
                    print("vertex_types", [(v[0], v[1]) for v in vertices], flush=True)
                    print("pairs", pairs, flush=True)
                    print("regions", regions, "outer", outer,
                          "target_offset", target_offset, flush=True)
                    print("region_corners", region_corners, flush=True)
                    if stop_on_hit:
                        return (type_multisets, planar, exact_disks,
                                one_copy_disks, len(one_copy_units))
    return (type_multisets, planar, exact_disks, one_copy_disks,
            len(one_copy_units))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-area", type=int, default=2)
    parser.add_argument("--max-area", type=int, default=4)
    parser.add_argument("--stop-on-hit", action="store_true")
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--shards", type=int, default=1)
    args = parser.parse_args()
    assert 0 <= args.shard < args.shards
    for area in range(args.min_area, args.max_area + 1):
        result = census(area, args.stop_on_hit, args.shard, args.shards)
        print(f"area={area} type_multisets={result[0]} planar={result[1]} "
              f"exact_target_disks={result[2]} one_copy_disks={result[3]} "
              f"one_copy_units={result[4]} shard={args.shard}/{args.shards}",
              flush=True)
        if result[2] and args.stop_on_hit:
            break


if __name__ == "__main__":
    main()
