#!/usr/bin/env python3
"""Random exact AGL(5,2) screen for the balanced Q96 forward-fan square."""

import argparse
import json
import random


N = 5
I = tuple(1 << i for i in range(N))
IDENTITY = (I, 0)
T = ((2, 3, 8, 12, 16), 0)
C = ((1, 2, 4, 8, 18), 8)
U = ((1, 2, 4, 8, 21), 24)


def linear_apply(matrix, value):
    return sum((bin(matrix[i] & value).count("1") & 1) << i for i in range(N))


def linear_multiply(left, right):
    rows = []
    for i in range(N):
        row = 0
        for k in range(N):
            if (left[i] >> k) & 1:
                row ^= right[k]
        rows.append(row)
    return tuple(rows)


def multiply(left, right):
    return (linear_multiply(left[0], right[0]),
            linear_apply(left[0], right[1]) ^ left[1])


def power(value, exponent):
    out = IDENTITY
    for _ in range(exponent):
        out = multiply(out, value)
    return out


def linear_inverse(matrix):
    rows = [matrix[i] | (1 << (N + i)) for i in range(N)]
    for col in range(N):
        pivot = next(row for row in range(col, N) if (rows[row] >> col) & 1)
        rows[col], rows[pivot] = rows[pivot], rows[col]
        for row in range(N):
            if row != col and ((rows[row] >> col) & 1):
                rows[row] ^= rows[col]
    return tuple((row >> N) & ((1 << N) - 1) for row in rows)


def inverse(value):
    matrix_inverse = linear_inverse(value[0])
    return matrix_inverse, linear_apply(matrix_inverse, value[1])


def conjugate(conjugator, value):
    return multiply(multiply(conjugator, value), inverse(conjugator))


def random_affine(rng):
    matrix = list(I)
    for _ in range(24):
        if rng.randrange(2):
            first, second = rng.sample(range(N), 2)
            matrix[first], matrix[second] = matrix[second], matrix[first]
        else:
            target, source = rng.sample(range(N), 2)
            matrix[target] ^= matrix[source]
    return tuple(matrix), rng.randrange(1 << N)


def permutation(value):
    return tuple(linear_apply(value[0], point) ^ value[1] for point in range(1 << N))


def compose(left, right):
    return tuple(left[right[point]] for point in range(len(left)))


def generated_order(generators, cap=1000):
    generators = tuple(permutation(value) for value in generators)
    identity = tuple(range(1 << N))
    seen = {identity}
    todo = [identity]
    while todo:
        old = todo.pop()
        for generator in generators:
            new = compose(old, generator)
            if new not in seen:
                seen.add(new)
                todo.append(new)
                if len(seen) > cap:
                    return len(seen)
    return len(seen)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=2_000_000)
    parser.add_argument("--seed", type=int, default=19243)
    args = parser.parse_args()
    rng = random.Random(args.seed)

    assert power(T, 3) == IDENTITY
    assert power(C, 2) == power(U, 2) == IDENTITY
    assert multiply(C, U) == multiply(U, C)
    assert power(multiply(C, T), 3) == power(multiply(U, T), 3) == IDENTITY
    assert generated_order((C, U, T), 100) == 96

    r_candidates = []
    z_candidates = []
    s_candidates = []
    samples = max(50_000, args.trials // 4)
    for _ in range(samples):
        conjugator = random_affine(rng)
        order_three = conjugate(conjugator, T)
        if (multiply(multiply(U, order_three), U) == inverse(order_three)
                and multiply(order_three, C) == multiply(C, order_three)):
            r_candidates.append(order_three)
        if (multiply(multiply(C, order_three), C) == inverse(order_three)
                and multiply(order_three, U) == multiply(U, order_three)):
            z_candidates.append(order_three)

        involution = conjugate(conjugator, C)
        if multiply(multiply(involution, T), involution) == inverse(T):
            q = IDENTITY
            for factor in (T, C, involution, C, inverse(T), C,
                           multiply(involution, T), C):
                q = multiply(q, factor)
            if q == IDENTITY and generated_order((T, involution, C), 30) == 24:
                s_candidates.append(involution)

    r_candidates = list(dict.fromkeys(r_candidates))
    z_candidates = list(dict.fromkeys(z_candidates))
    s_candidates = list(dict.fromkeys(s_candidates))
    for _ in range(args.trials):
        if not r_candidates or not z_candidates or not s_candidates:
            break
        r = rng.choice(r_candidates)
        z = rng.choice(z_candidates)
        if multiply(r, z) != multiply(z, r):
            continue
        s = rng.choice(s_candidates)
        b = multiply(s, T)
        if power(multiply(inverse(r), b), 3) != IDENTITY:
            continue
        if power(multiply(z, b), 3) != IDENTITY:
            continue
        if generated_order((r, z, b), 200) != 144:
            continue
        if generated_order((r, z, C, U), 50) != 36:
            continue
        print(json.dumps({
            "found": True,
            "seed": args.seed,
            "r": r,
            "z": z,
            "s": s,
            "b": b,
            "ambient_generated_order": generated_order((C, U, T, r, z, s), 100000),
        }, indent=2))
        return

    print(json.dumps({
        "found": False,
        "seed": args.seed,
        "trials": args.trials,
        "r_candidates": len(r_candidates),
        "z_candidates": len(z_candidates),
        "s_candidates": len(s_candidates),
    }, indent=2))


if __name__ == "__main__":
    main()
