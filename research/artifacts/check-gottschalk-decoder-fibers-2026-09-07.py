#!/usr/bin/env python3
"""Exact finite replay on F_2; no finite quotient or claimed open-case example.

Run from the repository root and redirect stdout to the companion JSON.
The mathematical infinite-group proof is in the adjacent Markdown artifact.
"""

import itertools
import json
import random


E = ()
S = (1,)
T = (2,)


def mul(a, b):
    out = list(a)
    for letter in b:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def inv(a):
    return tuple(-letter for letter in reversed(a))


def prod(a, b):
    return {mul(x, y) for x in a for y in b}


def inverse(a):
    return {inv(x) for x in a}


def shift_set(h, a):
    return {mul(h, x) for x in a}


def a_value(x, g):
    return x.get(g, (0, 0))


N = {E, T}
M = {E, inv(T), S}
K = prod(N, M)


def tau(z):
    # tau(z)(g)=(z(gt),0), with finite zero-background dictionaries.
    return {mul(g, inv(T)): (bit, 0) for g, bit in z.items() if bit}


def sigma(x):
    # sigma(a,b)(g)=a(gt^-1) XOR (b(g) AND b(gs)).
    out = {}
    for g in prod(set(x), inverse(M)):
        bit = a_value(x, mul(g, inv(T)))[0] ^ (
            a_value(x, g)[1] & a_value(x, mul(g, S))[1]
        )
        if bit:
            out[g] = bit
    return out


def retract(x):
    return tau(sigma(x))


def normalized_a(x):
    return {g: value for g, value in x.items() if value != (0, 0)}


def patch(x, h, core, local):
    out = dict(x)
    for k in core:
        g = mul(h, k)
        value = a_value(local, k)
        if value == (0, 0):
            out.pop(g, None)
        else:
            out[g] = value
    return out


def ball(radius):
    points = {E}
    for _ in range(radius):
        points |= prod(points, {S, inv(S), T, inv(T)})
    return points


def main():
    assert mul(S, T) != mul(T, S)
    assert prod(N, M) != prod(M, N)
    assert all(mul(g, inv(g)) == E for g in ball(4))

    window = sorted(ball(1))
    split_cases = 0
    for bits in itertools.product((0, 1), repeat=len(window)):
        z = {g: bit for g, bit in zip(window, bits) if bit}
        assert sigma(tau(z)) == z
        split_cases += 1

    retraction_cases = 0
    symbols = tuple(itertools.product((0, 1), repeat=2))
    for values in itertools.product(symbols, repeat=len(window)):
        x = normalized_a(dict(zip(window, values)))
        rx = retract(x)
        assert retract(rx) == rx
        assert sigma(rx) == sigma(x)
        retraction_cases += 1

    # A nonzero local reverse defect, then the proof's truncation to K.
    x = {T: (0, 1), mul(T, S): (0, 1)}
    assert a_value(retract(x), E) != a_value(x, E)
    u = normalized_a({g: a_value(x, g) for g in K})
    v = retract(u)
    assert sigma(u) == sigma(v) and u != v
    support_bound = prod(K, inverse(K))
    assert set(u) | set(v) <= support_bound
    d = {g for g in set(u) | set(v) if a_value(u, g) != a_value(v, g)}
    assert E in d
    h_set = prod(prod(d, inverse(M)), M)
    w_set = prod(h_set, N)
    assert d <= prod(d, inverse(M)) <= h_set <= w_set
    z0 = sigma(u)
    p = {g: z0.get(g, 0) for g in w_set}

    centers = []
    occupied = set()
    for i in range(1, 100):
        h = (1,) * (8 * i)
        translated = shift_set(h, w_set)
        if translated.isdisjoint(occupied):
            centers.append(h)
            occupied |= translated
        if len(centers) == 5:
            break
    assert len(centers) == 5

    rng = random.Random(20260907)
    # Vary finite outside contexts, including sites just outside the guards.
    context_pool = prod(occupied, ball(1)) - occupied
    packing_cases = 0
    for _ in range(8):
        z = {g: 1 for g in sorted(context_pool) if rng.randrange(2)}
        for h in centers:
            for k in w_set:
                g = mul(h, k)
                if p[k]:
                    z[g] = p[k]
                else:
                    z.pop(g, None)
        preferred = tau(z)
        for h in centers:
            assert all(a_value(preferred, mul(h, k)) == a_value(v, k)
                       for k in h_set)
        configurations = set()
        for bits in itertools.product((0, 1), repeat=len(centers)):
            candidate = preferred
            for bit, h in zip(bits, centers):
                if bit:
                    candidate = patch(candidate, h, d, u)
            assert sigma(candidate) == z
            for bit, h in zip(bits, centers):
                assert a_value(candidate, h) == a_value(u if bit else v, E)
            configurations.add(tuple(sorted(candidate.items())))
            packing_cases += 1
        assert len(configurations) == 2 ** len(centers)

    # The guard cannot be discarded even for this exact split pair.
    unguarded = patch(tau({}), E, d, u)
    assert sigma(unguarded) != {}
    assert sigma(unguarded) == {T: 1}

    # Rectangular projection: fibers have two choices per site while the
    # section-supported conditional measure has one. This records exact
    # supports; it does not infer entropy from cardinality.
    section_conditional_sizes = {}
    ambient_fiber_sizes = {}
    for output in (0, 1):
        ambient = [symbol for symbol in symbols if symbol[0] == output]
        supported = [symbol for symbol in ambient if symbol[1] == 0]
        assert len(ambient) == 2 and supported == [(output, 0)]
        ambient_fiber_sizes[str(output)] = len(ambient)
        section_conditional_sizes[str(output)] = len(supported)

    result = {
        "status": "passed",
        "scope": "exact finite-support calculations in the infinite free group F_2",
        "alphabet_sizes": {"encoder_input": 2, "encoder_output": 4},
        "not_a_gottschalk_counterexample": True,
        "lean_verified": False,
        "general_conjecture_proved": False,
        "reduced_word_inverse_checks": len(ball(4)),
        "noncommuting_memories_checked": True,
        "split_identity_cases": split_cases,
        "idempotence_and_decoder_collision_cases": retraction_cases,
        "sets": {"N": len(N), "M": len(M), "K": len(K),
                 "K_K_inverse": len(support_bound), "D": len(d),
                 "H": len(h_set), "W": len(w_set)},
        "simultaneous_sites": len(centers),
        "outside_contexts": 8,
        "packed_preimage_checks": packing_cases,
        "distinct_preimages_per_context": 2 ** len(centers),
        "unguarded_patch_counterexample_checked": True,
        "projection_one_site_fiber_sizes": ambient_fiber_sizes,
        "section_conditional_support_sizes": section_conditional_sizes,
        "infinite_packing_and_genericity": "proved in Markdown; not inferred from this replay",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
