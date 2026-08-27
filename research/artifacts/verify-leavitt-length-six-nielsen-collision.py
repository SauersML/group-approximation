#!/usr/bin/env python3
"""Exact Reidemeister--Schreier check for the Nielsen-collision word.

This is deliberately a symbolic six-letter calculation.  It does not use a
finite quotient or truncate the Leavitt algebra.
"""


def rewrite(coefficients: tuple[str, ...], signs: tuple[int, ...], start: int):
    height = start
    word: list[tuple[str, int]] = []

    def append(letter: str, exponent: int = 1) -> None:
        if exponent == 0:
            return
        if letter == "z" and word and word[-1][0] == "z":
            exponent += word.pop()[1]
            if exponent:
                word.append((letter, exponent))
            return
        word.append((letter, exponent))

    for coefficient, sign in zip(coefficients, signs, strict=True):
        parity = height % 2
        z_height = (height - parity) // 2
        append("z", z_height)
        if coefficient != "1":
            append(f"{coefficient}{parity}")
        append("z", -z_height)
        height += sign

    assert sum(signs) % 2 == 0
    append("z", sum(signs) // 2)
    return tuple(word)


SIGNS = (1, 1, 1, 1, -1, -1)
COEFFICIENTS = ("a", "1", "a", "p", "e", "q")

R0 = rewrite(COEFFICIENTS, SIGNS, 0)
R1 = rewrite(COEFFICIENTS, SIGNS, 1)

assert R0 == (
    ("a0", 1),
    ("z", 1),
    ("a0", 1),
    ("p1", 1),
    ("z", 1),
    ("e0", 1),
    ("z", -1),
    ("q1", 1),
)
assert R1 == (
    ("a1", 1),
    ("z", 1),
    ("a1", 1),
    ("z", 1),
    ("p0", 1),
    ("e1", 1),
    ("q0", 1),
    ("z", -1),
)

# Starting each relator at its first z gives the six corner labels below.
H = ("q1*a0", "a0*p1", "e0")
K = ("a1", "a1", "p0*e1*q0")
assert K[0] == K[1]

print("degree:", sum(SIGNS))
print("R0:", R0)
print("R1:", R1)
print("H corners:", H)
print("K corners:", K)
print("formal atlas kernel word: k0*k1 (both involutions, both map to a1)")
