#!/usr/bin/env python3
"""Exact moved-vector screen for full-copy retractions of the degree-4 KL word.

Copy zero is fixed.  Each of copies 1,2,3 is either killed or mapped by an
inner automorphism whose conjugator is `p^k` or the coordinate packet
`p^k q p^-k`, or by a cycle conjugate of either proper prefix-corner
self-embedding, `0 <= k < 20`.  R0 uniquely determines z.  A reported
rejection is exact: one standard-module basis vector with an opaque tail is
moved by one of R1,R2,R3.  The screen is not a finite-dimensional truncation.
"""

from itertools import product

N = 20


def root(i, j, coefficient):
    return ("r", coefficient, i, j)


def inverse(word):
    out = []
    for factor in reversed(word):
        if factor[0] == "p":
            out.append(("p", -factor[1]))
        elif factor[0] == "cp":
            out.append(("cp", factor[1], -factor[2]))
        else:
            out.append(factor)
    return tuple(out)


def ring_action(coefficient, prefix):
    for kind, bit in reversed(coefficient):
        if kind == "s":
            prefix = bit + prefix
        else:
            if not prefix or prefix[0] != bit:
                return None
            prefix = prefix[1:]
    return prefix


def act(factor, vector):
    if factor[0] == "p":
        return {((coordinate + factor[1]) % N, prefix)
                for coordinate, prefix in vector}
    if factor[0] == "cp":
        _, bit, shift = factor
        return {((coordinate + shift) % N, prefix)
                if prefix.startswith(bit) else (coordinate, prefix)
                for coordinate, prefix in vector}
    _, coefficient, row, column = factor
    result = set(vector)
    for coordinate, prefix in vector:
        if coordinate == column:
            image = ring_action(coefficient, prefix)
            if image is not None:
                term = (row, image)
                if term in result:
                    result.remove(term)
                else:
                    result.add(term)
    return result


def evaluate(word, vector):
    for factor in reversed(word):
        vector = act(factor, vector)
    return vector


S0 = (("s", "0"),)
S1 = (("s", "1"),)
T0 = (("t", "0"),)
T1 = (("t", "1"),)
A = (root(0, 1, S0),)
E = (root(0, 1, T1),)
Q = (root(2, 3, S1), root(10, 11, T0))
P = (("p", 1),)
R = Q + P
C = (root(0, 2, S0),)
B = R + R + A + inverse(R) + inverse(R)
D = P + P + C + inverse(P) + inverse(P)


def image(word, choice):
    if choice is None:
        return ()
    family, k = choice
    shift = (("p", k),)
    if family == "p":
        conjugator = shift
        return conjugator + word + inverse(conjugator)
    if family == "q":
        conjugator = shift + Q + inverse(shift)
        return conjugator + word + inverse(conjugator)
    bit = family[-1]
    corner = []
    for factor in word:
        if factor[0] == "p":
            corner.append(("cp", bit, factor[1]))
        else:
            _, coefficient, row, column = factor
            corner.append(("r", (("s", bit),) + coefficient
                           + (("t", bit),), row, column))
    return shift + tuple(corner) + inverse(shift)


def moved(word):
    """Return one exact moved vector, or None after a broad witness screen."""
    depth = sum(sum(kind == "t" for kind, _ in factor[1])
                for factor in word if factor[0] == "r")
    if any(factor[0] == "cp" for factor in word):
        depth = max(depth, 1)
    patterns = {"0" * depth, "1" * depth,
                ("01" * ((depth + 1) // 2))[:depth],
                ("10" * ((depth + 1) // 2))[:depth]}
    for prefix in patterns:
        for coordinate in range(N):
            vector = {(coordinate, prefix)}
            if evaluate(word, vector) != vector:
                return coordinate, prefix
    return None


identity = ("p", 0)
choices = ((None,) + tuple(("p", k) for k in range(20))
           + tuple(("q", k) for k in range(20))
           + tuple(("corner0", k) for k in range(20))
           + tuple(("corner1", k) for k in range(20)))
survivors = []
rejected = [0, 0, 0]
for c1, c2, c3 in product(choices, repeat=3):
    cs = (identity, c1, c2, c3)
    z = inverse(
        image(R, cs[0]) + image(E, cs[1]) + image(A, cs[2])
        + image(C, cs[1]) + image(B, cs[3]) + image(D, cs[2])
        + image(P, cs[3]))
    relators = (
        image(R, cs[1]) + image(E, cs[2]) + image(A, cs[3])
        + image(C, cs[2]) + z + image(B, cs[0]) + inverse(z)
        + image(D, cs[3]) + z + image(P, cs[0]),
        image(R, cs[2]) + image(E, cs[3]) + z + image(A, cs[0])
        + inverse(z) + image(C, cs[3]) + z + image(B, cs[1])
        + image(D, cs[0]) + image(P, cs[1]),
        image(R, cs[3]) + z + image(E, cs[0]) + image(A, cs[1])
        + image(C, cs[0]) + image(B, cs[2]) + image(D, cs[1])
        + image(P, cs[2]),
    )
    for index, relator in enumerate(relators):
        if moved(relator) is not None:
            rejected[index] += 1
            break
    else:
        survivors.append((c1, c2, c3))

print(f"cases={len(choices) ** 3}")
print(f"rejected_by_R1_R2_R3={tuple(rejected)}")
print(f"witness_screen_survivors={len(survivors)}")
if survivors:
    print("survivors=", survivors)
