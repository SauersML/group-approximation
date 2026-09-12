#!/usr/bin/env python3
"""Dependency-free transcription checks for the seven-relator Titz gate.

This checks identities in free groups only.  The normal-closure argument for
the five deleted square relators is the written proof, not a computation.
"""


def reduce_word(word):
    result = []
    for letter in word:
        if result and result[-1] == -letter:
            result.pop()
        else:
            result.append(letter)
    return tuple(result)


def product(*words):
    return reduce_word(letter for word in words for letter in word)


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def power(word, exponent):
    if exponent < 0:
        return power(inverse(word), -exponent)
    return product(*(word for _ in range(exponent)))


def substitute(word, images):
    factors = []
    for letter in word:
        image = images[abs(letter)]
        factors.append(image if letter > 0 else inverse(image))
    return product(*factors)


def main():
    # Old free basis: x=1, y=2, z=3.
    x, y, z = (1,), (2,), (3,)
    A = product(x, power(y, -2))
    B = product(z, inverse(y), z)
    C = product(power(y, 2), x)
    E = product(inverse(y), power(z, 2))
    F = product(inverse(x), power(z, 2), inverse(y), x)
    H = product(power(z, 2), inverse(y))

    assert B == product(z, E, inverse(z))
    assert H == product(y, E, inverse(y))
    assert F == product(inverse(x), H, x)

    # New free basis: c=1, e=2, r=3.
    c, e, r = (1,), (2,), (3,)
    Y = product(power(r, 2), inverse(e))
    X = product(power(Y, -2), c)
    old_to_new = {1: X, 2: Y, 3: r}
    new_to_old = {1: C, 2: E, 3: z}

    # Forward substitution recovers the new generators.
    assert substitute(C, old_to_new) == c
    assert substitute(E, old_to_new) == e
    assert substitute(z, old_to_new) == r

    # Reverse substitution recovers the old generators.
    assert substitute(X, new_to_old) == x
    assert substitute(Y, new_to_old) == y
    assert substitute(r, new_to_old) == z

    # The separating word is transported literally in both directions.
    assert substitute(power(y, 8), old_to_new) == power(Y, 8)
    assert substitute(power(Y, 8), new_to_old) == power(y, 8)
    print("all free-word checks passed")


if __name__ == "__main__":
    main()
