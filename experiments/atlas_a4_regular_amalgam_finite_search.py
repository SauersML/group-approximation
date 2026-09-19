#!/usr/bin/env python3
"""Search the canonical 144-point regular amalgam for the second S3.

The carrier ``C=(A4 x A4)`` acts regularly.  Its common ``C3 x C3`` subgroup
has sixteen orbits.  Pairing those orbits and applying ``(i,j)->(i,-j)``
constructs eight regular copies of ``F=C3 x S3`` on the same 144 points.
Thus every solution found here preserves the exact regular margins of F and C.
"""

import argparse
import json
import math
from itertools import permutations, product


def compose(left, right):
    return tuple(left[right[index]] for index in range(len(left)))


def inverse(value):
    result = [0] * len(value)
    for source, target in enumerate(value):
        result[target] = source
    return tuple(result)


def power(value, exponent):
    result = tuple(range(len(value)))
    for _ in range(exponent):
        result = compose(result, value)
    return result


I4 = (0, 1, 2, 3)
RHO = (1, 2, 0, 3)
BETA = (1, 0, 3, 2)


def parity(value):
    inversions = sum(value[i] > value[j] for i in range(4)
                     for j in range(i + 1, 4))
    return inversions % 2


A4 = tuple(value for value in permutations(range(4)) if parity(value) == 0)
A4_INDEX = {value: index for index, value in enumerate(A4)}


def a4_mul(left, right):
    return compose(left, right)


POINTS = tuple(product(A4, repeat=2))
POINT_INDEX = {value: index for index, value in enumerate(POINTS)}
IDENTITY = tuple(range(len(POINTS)))


def left_regular(pair):
    return tuple(POINT_INDEX[(a4_mul(pair[0], first),
                              a4_mul(pair[1], second))]
                 for first, second in POINTS)


# Diagonal/anti-diagonal coordinates make the same involution B complete each
# C3 line with an A4: both RB and ZB have order three.
RHO_INV = a4_mul(RHO, RHO)
R = left_regular((RHO, RHO))
Z = left_regular((RHO, RHO_INV))
B = left_regular((BETA, BETA))


def left_coset_coordinates():
    rho_powers = (I4, RHO, a4_mul(RHO, RHO))
    unused = set(A4)
    coordinates = {}
    representatives = []
    while unused:
        representative = min(unused)
        orbit = tuple(a4_mul(rho_power, representative)
                      for rho_power in rho_powers)
        label = len(representatives)
        representatives.append(representative)
        for exponent, value in enumerate(orbit):
            coordinates[value] = (label, exponent)
            unused.remove(value)
    return representatives, coordinates


REPRESENTATIVES, COORDINATES = left_coset_coordinates()


def collision_involution(pairing_mask=1):
    # Pair orbit label k with k xor 1.  Preserve the r exponent and negate the
    # z exponent.  This is eight disjoint regular F=C3 x S3 actions.
    result = [None] * len(POINTS)
    rho_powers = (I4, RHO, a4_mul(RHO, RHO))
    for source, (first, second) in enumerate(POINTS):
        first_label, first_exponent = COORDINATES[first]
        second_label, second_exponent = COORDINATES[second]
        orbit_label = 4 * first_label + second_label
        target_label = orbit_label ^ pairing_mask
        target_first_label, target_second_label = divmod(target_label, 4)
        # In component coordinates the automorphism fixing r=(rho,rho) and
        # inverting z=(rho,rho^-1) swaps the two rho exponents.
        target_first = a4_mul(rho_powers[second_exponent],
                              REPRESENTATIVES[target_first_label])
        target_second = a4_mul(rho_powers[first_exponent],
                               REPRESENTATIVES[target_second_label])
        result[source] = POINT_INDEX[(target_first, target_second)]
    return tuple(result)


def semilinear_collision(unit):
    """Factor swap followed by right multiplication by (unit,unit^-1)."""
    unit_inverse = inverse(unit)
    return tuple(POINT_INDEX[(a4_mul(second, unit),
                              a4_mul(first, unit_inverse))]
                 for first, second in POINTS)


C = collision_involution()

GENERATORS = {"r": R, "R": power(R, 2), "z": Z, "Z": power(Z, 2),
              "c": C, "b": B}


def generated_order(generators):
    seen = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        old = frontier.pop()
        for generator in generators:
            new = compose(old, generator)
            if new not in seen:
                seen.add(new)
                frontier.append(new)
    return len(seen)


def permutation_order(value):
    seen = set()
    result = 1
    for start in range(len(value)):
        if start in seen:
            continue
        point = start
        length = 0
        while point not in seen:
            seen.add(point)
            point = value[point]
            length += 1
        result = result * length // math.gcd(result, length)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=8)
    parser.add_argument("--scan-pairings", action="store_true")
    parser.add_argument("--scan-semilinear", action="store_true")
    parser.add_argument("--certify-amalgam", action="store_true")
    args = parser.parse_args()

    assert power(R, 3) == IDENTITY and power(Z, 3) == IDENTITY
    assert power(B, 2) == IDENTITY and power(C, 2) == IDENTITY
    assert compose(R, Z) == compose(Z, R)
    assert compose(C, R) == compose(R, C)
    assert compose(compose(C, Z), C) == inverse(Z)
    assert power(compose(inverse(R), B), 3) == IDENTITY
    assert power(compose(Z, B), 3) == IDENTITY
    assert generated_order((R, Z, C)) == 18
    assert generated_order((R, Z, B)) == 144

    if args.scan_pairings:
        records = []
        for pairing_mask in range(1, 16):
            candidate_c = collision_involution(pairing_mask)
            bc_order = permutation_order(compose(B, candidate_c))
            records.append({"pairing_mask": pairing_mask,
                            "bc_order": bc_order})
        print(json.dumps(records, indent=2))
        return
    if args.scan_semilinear:
        records = []
        for unit in A4:
            candidate_c = semilinear_collision(unit)
            records.append({
                "unit": list(unit),
                "bc_order": permutation_order(compose(B, candidate_c)),
                "first_support_order": generated_order((R, Z, candidate_c)),
            })
        print(json.dumps(records, indent=2))
        return
    if args.certify_amalgam:
        swap_c = semilinear_collision(I4)
        assert power(swap_c, 2) == IDENTITY
        assert compose(swap_c, R) == compose(R, swap_c)
        assert compose(compose(swap_c, Z), swap_c) == inverse(Z)
        assert compose(swap_c, B) == compose(B, swap_c)
        h_order = generated_order((R, Z, B, swap_c))
        first_order = generated_order((R, Z, swap_c))
        carrier_order = generated_order((R, Z, B))
        v_order = generated_order((B, swap_c))
        assert (h_order, first_order, carrier_order, v_order) == (288, 18, 144, 4)

        # J=S3 x C2 on six points, with c the central C2 factor.  Tuple pairs
        # are composed componentwise; this also checks the collision word.
        i3 = (0, 1, 2)
        t3 = (1, 2, 0)
        b3 = (1, 0, 2)
        t3_inv = inverse(t3)
        s3 = compose(b3, t3_inv)
        assert power(t3, 3) == i3 and power(s3, 2) == i3
        assert compose(s3, t3) == b3
        q3 = compose(t3, compose(s3, compose(t3_inv, compose(s3, t3))))
        assert q3 == i3

        print(json.dumps({
            "ambient_symmetric_degree": 288,
            "H_order": h_order,
            "first_support_order": first_order,
            "carrier_order": carrier_order,
            "common_V4_order": v_order,
            "second_S3_order": 6,
            "J_order": 12,
            "Reg_H_restricted_V4_copies": 288 // 4,
            "24_Reg_J_restricted_V4_copies": 24 * (12 // 4),
            "collision_reduces_to": "t*s*t^-1*s*t=1",
        }, indent=2, sort_keys=True))
        return

    seen = {IDENTITY: ""}
    frontier = [IDENTITY]
    tested = 0
    s3_candidates = 0
    solutions = []
    for length in range(args.radius + 1):
        next_frontier = []
        for T in frontier:
            tested += 1
            word = seen[T]
            if power(T, 3) != IDENTITY or T == IDENTITY:
                pass
            elif compose(compose(B, T), B) == inverse(T):
                s3_candidates += 1
                S = compose(B, inverse(T))
                collision = compose(
                    T, compose(C, compose(S, compose(C, compose(inverse(T),
                    compose(C, compose(S, compose(T, C))))))))
                if collision == IDENTITY:
                    assert generated_order((T, S)) == 6
                    solutions.append(word)
                    print("SOLUTION", word, flush=True)
            if length < args.radius:
                for letter, generator in GENERATORS.items():
                    new = compose(T, generator)
                    if new not in seen:
                        seen[new] = word + letter
                        next_frontier.append(new)
        frontier = next_frontier
        print(f"radius={length} images={tested} s3={s3_candidates} "
              f"solutions={len(solutions)}", flush=True)

    print(json.dumps({
        "radius": args.radius,
        "distinct_images": tested,
        "s3_candidates": s3_candidates,
        "solutions": solutions,
        "first_support_order": generated_order((R, Z, C)),
        "carrier_order": generated_order((R, Z, B)),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
