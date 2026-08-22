#!/usr/bin/env python3
"""Screen canonical internal solutions for the composite-Omega KL word.

Every negative result is certified by one explicit basis vector in the
faithful infinite-binary-word module of the Leavitt algebra.  The finite
prefix is followed by one common opaque tail, so this is not a truncation of
the ring or group.
"""

from itertools import product

N = 20
TAIL = "00101100110100101101001101011101010110100110101"


def ring_action(coefficient, bits):
    for kind, bit in reversed(coefficient):
        if kind == "s":
            bits = bit + bits
        elif not bits or bits[0] != bit:
            return None
        else:
            bits = bits[1:]
    return bits


def toggle(vector, term):
    if term in vector:
        vector.remove(term)
    else:
        vector.add(term)


def act(factor, vector):
    if factor[0] == "p":
        return {((coordinate + factor[1]) % N, bits)
                for coordinate, bits in vector}
    _, coefficient, row, column = factor
    result = set(vector)
    for coordinate, bits in vector:
        if coordinate == column:
            image = ring_action(coefficient, bits)
            if image is not None:
                toggle(result, (row, image))
    return result


def evaluate(word, vector):
    for factor in reversed(word):
        vector = act(factor, vector)
    return vector


def inverse(word):
    result = []
    for factor in reversed(word):
        if factor[0] == "p":
            result.append(("p", -factor[1]))
        else:
            # All displayed elementary roots square to zero in their matrix
            # position, so their characteristic-two transvections are
            # involutions.  Composite words are reversed factor by factor.
            result.append(factor)
    return tuple(result)


def root(row, column, coefficient):
    return ("r", coefficient, row, column)


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


def kl_word(t):
    # W'=r t e t a t^-1 c t^2 b t^-1 d t p t.
    return (R + t + E + t + A + inverse(t) + C + t + t + B
            + inverse(t) + D + t + P + t)


CANDIDATES = {
    "1": (),
    "p": P,
    "p^-1": inverse(P),
    "q": Q,
    "r": R,
    "r^-1": inverse(R),
    "a": A,
    "e": E,
    "c": C,
    "b": B,
    "d": D,
}

witnesses = {}
prefixes = ("".join(bits) + TAIL for depth in range(5)
            for bits in product("01", repeat=depth))
tests = tuple((coordinate, bits) for bits in prefixes
              for coordinate in range(N))
for name, candidate in CANDIDATES.items():
    word = kl_word(candidate)
    for test in tests:
        source = {test}
        image = evaluate(word, source)
        if image != source:
            witnesses[name] = (test, tuple(sorted(image)))
            break

assert set(witnesses) == set(CANDIDATES), set(CANDIDATES) - set(witnesses)

for name in CANDIDATES:
    test, image = witnesses[name]
    print(f"{name}: {test} -> {image}")
print("PASS: no canonical packet word is an internal solution of W'=1")
