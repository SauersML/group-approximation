#!/usr/bin/env python3
"""Compile exact carriers/boundary for class N(0;115)."""


def reduce_coefficient(word):
    out = []
    for letter in word:
        if out and out[-1] == (letter[0], -letter[1]):
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def syllable(copy, *names):
    return copy, tuple((name, 1) for name in names)


def multiply(*words):
    out = []
    for word in words:
        for copy, coefficient in word:
            if not coefficient:
                continue
            if out and out[-1][0] == copy:
                coefficient = reduce_coefficient(out[-1][1] + coefficient)
                out.pop()
                if coefficient:
                    out.append((copy, coefficient))
            else:
                out.append((copy, coefficient))
    return tuple(out)


def inverse(word):
    return tuple((copy, tuple((name, -sign)
                              for name, sign in reversed(coefficient)))
                 for copy, coefficient in reversed(word))


H = (
    syllable(0, "g9"), syllable(1, "g10"), syllable(0, "g11"),
    syllable(1, "g12"), syllable(2, "g13"), syllable(3, "g0"),
    syllable(2, "g1"), syllable(1, "g2"), syllable(0, "g3"),
    syllable(1, "g4"), syllable(0, "g5"), syllable(1, "g6"),
    syllable(2, "g7"), syllable(3, "g8"),
)
A0 = (syllable(3, "g1"), syllable(2, "g2"), syllable(1, "g3"),
      syllable(2, "g4"), syllable(1, "g5"), syllable(2, "g6"),
      syllable(3, "g7"))
B0 = (syllable(0, "g8"), syllable(1, "g9"), syllable(2, "g10"),
      syllable(1, "g11"), syllable(2, "g12"), syllable(3, "g13"))
C0 = (syllable(0, "g0"),)
A1 = (syllable(3, "g2"), syllable(2, "g3"), syllable(3, "g4"),
      syllable(2, "g5"), syllable(3, "g6"))
B1 = (syllable(0, "g7"), syllable(1, "g8"), syllable(2, "g9"),
      syllable(3, "g10"), syllable(2, "g11"), syllable(3, "g12"))
C1 = (syllable(0, "g13"), syllable(1, "g0"), syllable(0, "g1"))
E1 = (syllable(3, "g3"),)
E2 = (syllable(0, "g4"),)
E3 = (syllable(3, "g5"),)
E4 = (syllable(0, "g6"), syllable(1, "g7"),
      syllable(2, "g8"), syllable(3, "g9"))
E5 = (syllable(0, "g10"),)
E6 = (syllable(3, "g11"),)
E7 = (syllable(0, "g12"), syllable(1, "g13"),
      syllable(2, "g0"), syllable(1, "g1"), syllable(0, "g2"))

# Standard trivalent orientations and valence-seven assignment
# T0=id0^-1, T1=id4^-1, T2T3T4T5T6=id5.
R0 = multiply(H, A0, H, E1)
R2 = multiply(inverse(H), C0, H, A1)
R4 = multiply(inverse(H), C1, inverse(H), E2)
K = multiply(inverse(H), B0, inverse(H), B1,
             H, E3, inverse(H), E4, inverse(H), E5,
             H, E6, inverse(H), E7)


def show(name, word):
    print(f"{name}_syllables={len(word)}")
    print(f"{name}_colors=" + ",".join(str(copy) for copy, _ in word))
    for index, (copy, coefficient) in enumerate(word):
        text = " ".join(name + ("^-1" if sign < 0 else "")
                        for name, sign in coefficient)
        print(f"{name}[{index}]={copy}:{text}")


def project(word, target):
    coefficient = ()
    for copy, syllable_word in word:
        if copy == target:
            coefficient = reduce_coefficient(coefficient + syllable_word)
    return coefficient


def show_projections(name, word):
    for target in range(4):
        coefficient = project(word, target)
        text = " ".join(letter + ("^-1" if sign < 0 else "")
                        for letter, sign in coefficient)
        print(f"{name}_projection_{target}={text or '1'}")


def main():
    for name, word in (("R0", R0), ("R2", R2), ("R4", R4), ("K", K)):
        show(name, word)
        show_projections(name, word)


if __name__ == "__main__":
    main()
