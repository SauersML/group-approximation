#!/usr/bin/env python3
"""Substitute the four exact copy-retraction equations in three-winner words."""


VARIABLES = ("p", "u", "v", "w", "x", "y", "z", "a", "b", "c", "d", "e")


def reduce_coefficient(word):
    out = []
    for letter in word:
        if out and out[-1] == (letter[0], -letter[1]):
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def inverse_coefficient(word):
    return tuple((name, -sign) for name, sign in reversed(word))


SUBSTITUTION = {
    "c": (("p", -1), ("e", -1)),
    "x": (("v", -1), ("u", -1)),
    "d": (("y", -1), ("w", -1), ("p", -1)),
    "b": (("w", -1), ("u", -1), ("p", 1), ("w", 1), ("y", 1)),
}


def substitute_coefficient(word):
    out = ()
    for name, sign in word:
        image = SUBSTITUTION.get(name, ((name, 1),))
        if sign < 0:
            image = inverse_coefficient(image)
        out = reduce_coefficient(out + image)
    return out


def syllable(copy, *names):
    return copy, tuple((name, 1) for name in names)


def multiply(*words):
    out = []
    for word in words:
        for copy, coefficient in word:
            coefficient = substitute_coefficient(coefficient)
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
    return tuple((copy, inverse_coefficient(coefficient))
                 for copy, coefficient in reversed(word))


H = (
    syllable(0, "a"), syllable(1, "b"), syllable(2, "c"),
    syllable(1, "d"), syllable(2, "e", "p"), syllable(1, "u", "v"),
    syllable(2, "w"), syllable(1, "x"), syllable(2, "y"),
    syllable(3, "z"),
)
A0 = (syllable(3, "p"), syllable(2, "u", "v"), syllable(3, "w"),
      syllable(2, "x"), syllable(3, "y"))
B0 = (syllable(0, "z"), syllable(1, "a"), syllable(2, "b"),
      syllable(3, "c"), syllable(2, "d"), syllable(3, "e"))
B1 = (syllable(0, "v"), syllable(1, "w"), syllable(0, "x"),
      syllable(1, "y"), syllable(2, "z"), syllable(3, "a"))
C1 = (syllable(0, "b"), syllable(1, "c"), syllable(0, "d"),
      syllable(1, "e", "p"), syllable(0, "u"))
E1 = (syllable(3, "u", "v"),)
E2 = (syllable(0, "w"),)
E3 = (syllable(3, "x"),)
E4 = (syllable(0, "y"), syllable(1, "z"), syllable(2, "a"),
      syllable(3, "b"))
E5 = (syllable(0, "c"),)
E6 = (syllable(3, "d"),)
E7 = (syllable(0, "e", "p"),)

EQ0 = multiply(H, A0, inverse(H), E5, H, E6, inverse(H), E7)
EQ4 = multiply(inverse(H), C1, H, E1, inverse(H), E2, H, E3)
K = multiply(inverse(H), B0, inverse(H), B1, inverse(H), E4)


def show(name, word):
    print(f"{name}_syllables={len(word)}")
    print(f"{name}_colors=" + ",".join(str(copy) for copy, _ in word))
    for index, (copy, coefficient) in enumerate(word):
        text = " ".join(generator + ("^-1" if sign < 0 else "")
                        for generator, sign in coefficient)
        print(f"{name}[{index}]={copy}:{text}")


def main():
    # Directly replay all four coefficient retractions before using them.
    assert reduce_coefficient(SUBSTITUTION["c"] + (("e", 1), ("p", 1))) == ()
    assert reduce_coefficient((("u", 1), ("v", 1)) + SUBSTITUTION["x"]) == ()
    assert reduce_coefficient((("p", 1), ("w", 1), ("y", 1))
                              + SUBSTITUTION["d"]) == ()
    assert reduce_coefficient(SUBSTITUTION["b"] + SUBSTITUTION["d"]
                              + (("u", 1), ("w", 1))) == ()
    show("H", multiply(H))
    show("EQ0", EQ0)
    show("EQ4", EQ4)
    show("K", K)


if __name__ == "__main__":
    main()
