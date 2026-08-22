#!/usr/bin/env python3
"""Exact index-four rewrite of the affine Omega transport candidate."""


def rewrite(coefficients, signs, start):
    height = start
    word = []

    def append(letter, exponent=1):
        if not exponent:
            return
        if letter == "z" and word and word[-1][0] == "z":
            exponent += word.pop()[1]
            if exponent:
                word.append((letter, exponent))
        else:
            word.append((letter, exponent))

    for coefficient, sign in zip(coefficients, signs, strict=True):
        residue = height % 4
        z_height = (height - residue) // 4
        append("z", z_height)
        if coefficient != "1":
            append(f"{coefficient}{residue}")
        append("z", -z_height)
        height += sign
    append("z", 1)
    return tuple(word)


COEFFICIENTS = ("r", "1", "a", "c", "1", "e", "q", "p")
SIGNS = (1, 1, -1, 1, 1, -1, 1, 1)
RELATIONS = tuple(rewrite(COEFFICIENTS, SIGNS, start)
                  for start in range(4))

assert RELATIONS == (
    (("r0", 1), ("a2", 1), ("c1", 1), ("e3", 1),
     ("q2", 1), ("p3", 1), ("z", 1)),
    (("r1", 1), ("a3", 1), ("c2", 1), ("z", 1),
     ("e0", 1), ("z", -1), ("q3", 1), ("z", 1), ("p0", 1)),
    (("r2", 1), ("z", 1), ("a0", 1), ("z", -1),
     ("c3", 1), ("z", 1), ("e1", 1), ("q0", 1), ("p1", 1)),
    (("r3", 1), ("z", 1), ("a1", 1), ("c0", 1),
     ("e2", 1), ("q1", 1), ("p2", 1)),
)

print("degree:", sum(SIGNS))
for index, relation in enumerate(RELATIONS):
    print(f"R{index}:", relation)
print("pivot: z=p3^-1 q2 e3 c1 a2 r0^-1")
