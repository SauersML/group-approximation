#!/usr/bin/env python3
"""Exact witnesses for the three-gate length-six Leavitt candidate."""

N = 20


def normalize(prefix, tail):
    while prefix and prefix[-1] == tail:
        prefix = prefix[:-1]
    return prefix, tail


def ring_action(kind, bit, word):
    prefix, tail = word
    if kind == "s":
        return normalize(bit + prefix, tail)
    first = prefix[0] if prefix else tail
    if first != bit:
        return None
    return normalize(prefix[1:] if prefix else "", tail)


def toggle(values, value):
    if value in values:
        values.remove(value)
    else:
        values.add(value)


ROOT = {"a": ("s", "0"), "b": ("s", "1"),
        "c": ("t", "0"), "e": ("t", "1")}


def act(factor, vector):
    kind = factor[0]
    if kind == "p":
        power = factor[1]
        return {((coordinate + power) % N, word) for coordinate, word in vector}
    _, letter, i, j = factor
    result = set(vector)
    root_kind, bit = ROOT[letter]
    for coordinate, word in vector:
        if coordinate == j:
            image = ring_action(root_kind, bit, word)
            if image is not None:
                toggle(result, (i, image))
    return result


def evaluate(word, vector):
    for factor in reversed(word):
        vector = act(factor, vector)
    return vector


A = (("r", "a", 0, 1),)
E = (("r", "e", 0, 1),)
C = (("r", "b", 2, 3), ("r", "c", 10, 11))
P = (("p", 1),)

# At t=1 the coefficient product is A C P E.
specialization = A + C + P + E
test = {(0, normalize("001011", "0"))}
assert evaluate(specialization, test) != test

# Killing either coefficient copy forces z=p^-1.  The other relator leaves
# F=A p^-1 C p^-1 E p, which already moves coordinate 1 to coordinate 20.
residual = A + (("p", -1),) + C + (("p", -1),) + E + P
image = evaluate(residual, test)
assert image != test
assert any(coordinate == 19 for coordinate, _ in image)

print("PASS: t=1 is not a solution and both copy-killing retractions fail")

