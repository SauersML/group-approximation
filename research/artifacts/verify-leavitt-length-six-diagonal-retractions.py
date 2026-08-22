#!/usr/bin/env python3
"""Exact permutation/infinite-word tests for the L6 paired quotient.

The Leavitt algebra acts faithfully on the F2-vector space with basis the
infinite binary words.  The finite strings below are long prefixes of one
fixed infinite word; every tested expression inspects fewer than ten bits.
"""

N = 20
TAIL = "00101100110100101101001101011101010110100110101" * 3


def toggle(values, value):
    if value in values:
        values.remove(value)
    else:
        values.add(value)


def ring_action(generator, bits):
    kind, bit = generator
    if kind == "s":
        return [bit + bits]
    if bits[0] != bit:
        return []
    return [bits[1:]]


def root_action(generator, vector, i=0, j=1):
    result = set(vector)
    for coordinate, bits in vector:
        if coordinate == j:
            for image in ring_action(generator, bits):
                toggle(result, (i, image))
    return result


def cycle_power(power):
    return tuple((i + power) % N for i in range(N))


def compose(left, right):
    return tuple(left[right[i]] for i in range(N))


def permutation_action(permutation, vector):
    return {(permutation[coordinate], bits) for coordinate, bits in vector}


def conjugate_permutation(permutation, power):
    return compose(cycle_power(power), compose(permutation, cycle_power(-power)))


def conjugate_root(generator, power, vector):
    vector = permutation_action(cycle_power(-power), vector)
    vector = root_action(generator, vector)
    return permutation_action(cycle_power(power), vector)


P = cycle_power(1)

ROOTS = {
    "a": ("s", "0"),
    "b": ("s", "1"),
    "c": ("t", "0"),
    "e": ("t", "1"),
}
STAR = {
    ("s", "0"): ("t", "0"),
    ("s", "1"): ("t", "1"),
    ("t", "0"): ("s", "0"),
    ("t", "1"): ("s", "1"),
}


def coefficient_action(name, model, power, vector):
    letter, copy = name
    if copy == "0":
        if letter == "d":
            return permutation_action(P, vector)
        return root_action(ROOTS[letter], vector)

    if model == "inner":
        if letter == "d":
            return permutation_action(conjugate_permutation(P, power), vector)
        return conjugate_root(ROOTS[letter], power, vector)

    # Ad(p^power) after g |-> (g*)^-1.  The duality swaps roots 12 and 21.
    if letter == "d":
        return permutation_action(P, vector)
    vector = permutation_action(cycle_power(-power), vector)
    vector = root_action(STAR[ROOTS[letter]], vector, i=1, j=0)
    return permutation_action(cycle_power(power), vector)


R0 = (("g", "a0"), ("g", "b1"), ("z", 1), ("g", "c0"),
      ("g", "d1"), ("z", 1), ("g", "e0"), ("z", -1))
R1 = (("g", "a1"), ("z", 1), ("g", "b0"), ("g", "c1"),
      ("z", 1), ("g", "d0"), ("g", "e1"), ("z", -1))


def evaluate(relation, model, power, z_power, vector):
    for kind, value in reversed(relation):
        if kind == "z":
            vector = permutation_action(cycle_power(z_power * value), vector)
        else:
            vector = coefficient_action(value, model, power, vector)
    return vector


tests = tuple((coordinate, TAIL) for coordinate in range(N))

# The one-copy-killing residual
# F=a b p^(-1)c b p^(-1)e p b has a surviving cycle entry.
factors = (("g", "a0"), ("g", "b0"), ("z", -1), ("g", "c0"),
           ("g", "b0"), ("z", -1), ("g", "e0"), ("z", 1),
           ("g", "b0"))
f_test = {(3, TAIL)}
f_image = evaluate(factors, "inner", 0, 1, f_test)
assert f_image != f_test
assert (2, TAIL) in f_image

for model in ("inner", "prefix_dual"):
    solutions = []
    for power in range(N):
        for z_power in range(N):
            if all(
                evaluate(R0, model, power, z_power, {test}) == {test}
                and evaluate(R1, model, power, z_power, {test}) == {test}
                for test in tests
            ):
                solutions.append((power, z_power))
    assert not solutions, (model, solutions)

print("PASS: no cycle-inner or prefix-dual diagonal retraction with z a cycle power")
