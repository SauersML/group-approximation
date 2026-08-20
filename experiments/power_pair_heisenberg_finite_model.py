#!/usr/bin/env python3
"""Exhaustively verify the p=5 Heisenberg model of the 2/3 power-pair HNN cell."""

import json
from itertools import product


P = 5
M = 2
N = 3


def mul(g, h):
    a, b, c = g
    x, y, z = h
    return ((a + x) % P, (b + y) % P, (c + z + a * y) % P)


def inv(g):
    a, b, c = g
    return ((-a) % P, (-b) % P, (-c + a * b) % P)


def sigma(k, g):
    a, b, c = g
    return (k * a % P, k * b % P, k * k * c % P)


def comm(g, h):
    return mul(mul(mul(g, h), inv(g)), inv(h))


def main():
    elements = list(product(range(P), repeat=3))
    identity = (0, 0, 0)
    x = (1, 0, 0)
    y = (0, 1, 0)

    hom_checks = {}
    bijective_checks = {}
    for k in (M, N):
        hom_checks[str(k)] = all(
            sigma(k, mul(g, h)) == mul(sigma(k, g), sigma(k, h))
            for g in elements
            for h in elements
        )
        bijective_checks[str(k)] = len({sigma(k, g) for g in elements}) == len(elements)

    carrier = list(product(elements, repeat=2))

    def left_h0(h, point):
        u, v = point
        return (mul(h, u), v)

    def left_delta(h, point):
        u, v = point
        return (mul(sigma(M, h), u), mul(sigma(N, h), v))

    def stable(point):
        u, v = point
        return (sigma(M, u), mul(sigma(N, u), v))

    stable_bijective = len({stable(point) for point in carrier}) == len(carrier)
    intertwining = all(
        stable(left_h0(h, point)) == left_delta(h, stable(point))
        for h in elements
        for point in carrier
    )

    result = {
        "prime": P,
        "power_pair": [M, N],
        "heisenberg_order": len(elements),
        "regular_carrier_size": len(carrier),
        "scaling_maps_are_homomorphisms": hom_checks,
        "scaling_maps_are_bijective": bijective_checks,
        "stable_permutation_is_bijective": stable_bijective,
        "stable_permutation_intertwines_every_edge_element": intertwining,
        "generator_commutator": comm(x, y),
        "generator_commutator_is_nontrivial": comm(x, y) != identity,
        "all_checks_pass": (
            all(hom_checks.values())
            and all(bijective_checks.values())
            and stable_bijective
            and intertwining
            and comm(x, y) != identity
        ),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
