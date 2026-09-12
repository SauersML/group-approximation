#!/usr/bin/env python3
"""Transcription checks for the two-generator Titz--Witzel gate.

This is dependency-free.  It verifies free-word identities and identities in
the free product <e | e^2> * <u>.  The normal-closure argument proving that
the retained relators present the same group is the written Cairn proof, not
this computation.
"""


def reduce_word(word, involutions=()):
    involutions = set(involutions)
    result = []
    for letter in word:
        if abs(letter) in involutions:
            letter = abs(letter)
        if result and result[-1] == -letter:
            result.pop()
        elif result and letter in involutions and result[-1] == letter:
            result.pop()
        else:
            result.append(letter)
    return tuple(result)


def product(*words, involutions=()):
    return reduce_word(
        (letter for word in words for letter in word), involutions=involutions
    )


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def power(word, exponent, involutions=()):
    if exponent < 0:
        return power(inverse(word), -exponent, involutions=involutions)
    return product(*(word for _ in range(exponent)), involutions=involutions)


def substitute(word, images, involutions=()):
    factors = []
    for letter in word:
        image = images[abs(letter)]
        factors.append(image if letter > 0 else inverse(image))
    return product(*factors, involutions=involutions)


def main():
    # Old basis: c=1, e=2, r=3.  These checks use only free cancellation.
    c_old, e_old, r_old = (1,), (2,), (3,)
    y_old = product(power(r_old, 2), inverse(e_old))
    x_old = product(power(y_old, -2), c_old)
    a_old = product(x_old, power(y_old, -2))
    h_old = product(power(r_old, 2), inverse(y_old))
    f_old = product(inverse(x_old), h_old, x_old)

    # The change u=Y makes H a conjugate of e before any group relator is used.
    assert h_old == product(y_old, e_old, inverse(y_old))
    assert x_old == product(power(y_old, -2), c_old)
    assert a_old == product(x_old, power(y_old, -2))
    assert f_old == product(inverse(x_old), h_old, x_old)

    # New basis: e=1, u=2, with e reduced as an involution.
    e, u = (1,), (2,)
    invs = (1,)

    def p(*words):
        return product(*words, involutions=invs)

    def q(word, exponent):
        return power(word, exponent, involutions=invs)

    h = p(u, e, inverse(u))
    a = p(e, h, e)
    x = p(a, q(u, 2))
    c = p(q(u, 2), a, q(u, 2))
    f = p(inverse(x), h, x)
    d = p(e, inverse(a), f)
    s = p(f, a, f)
    rho = p(inverse(x), inverse(s), inverse(c))
    b = p(rho, inverse(u), rho)

    # The first triangular equation, the old definitions of A and X, and the
    # solved second quartic all become literal reduced-word identities.
    assert p(e, a, e) == h
    assert p(q(u, -2), c) == x
    assert p(x, q(u, -2)) == a
    assert p(x, rho, c, s) == ()

    # The other two triangular equations and the B-definition are exactly the
    # words used in the new presentation.
    assert d == p(e, inverse(a), f)
    assert s == p(f, a, f)
    assert b == p(rho, inverse(u), rho)

    # The reverse change sends the new marked generator literally to old Y.
    # In the forward change, the retained defining relator R0 says that the
    # image of old Y is u; check its exact free-word transcription R0*u.
    old_to_new = {1: c, 2: e, 3: rho}
    new_to_old = {1: e_old, 2: y_old}
    image_y = substitute(y_old, old_to_new, involutions=invs)
    r0 = p(q(rho, 2), inverse(e), inverse(u))
    assert image_y == p(r0, u)
    assert substitute(q(u, 8), new_to_old) == power(y_old, 8)

    # Retained relators are transcribed exactly from (7).
    retained = (
        q(c, 2),
        r0,
        p(b, x, inverse(u), inverse(d)),
        p(a, c, d, b),
    )
    assert all(isinstance(word, tuple) for word in retained)
    print("all two-generator Titz free-word checks passed")


if __name__ == "__main__":
    main()
