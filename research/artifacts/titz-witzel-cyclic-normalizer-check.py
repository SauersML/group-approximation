#!/usr/bin/env python3
"""Exact symbolic check for the cyclic-normalizer Titz gate obstruction.

The coefficient pair (a,b) denotes a+b*q in Z[q]/(q^2-1).  A group
element is stored in normal form u^(a+b*q) e^parity, under

    e^2 = 1,                 e u e = u^q.

This checker is dependency-free and proves no analytic estimate.  It checks
the word transcription and the exponent identity used in the written proof.
"""


def reduce_word(word):
    result = []
    for letter in word:
        if abs(letter) == 1:  # 1=e and e is an involution
            letter = 1
        if result and (
            result[-1] == -letter or (letter == 1 and result[-1] == 1)
        ):
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


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def multiply_by_q(x):
    # q(a+bq)=b+aq because q^2=1.
    return x[1], x[0]


def normal_form(word):
    """Return (exponent_pair, parity) for u^exponent e^parity."""
    exponent = (0, 0)
    parity = 0
    for letter in word:
        if abs(letter) == 1:
            letter_exponent, letter_parity = (0, 0), 1
        else:
            letter_exponent = (1 if letter > 0 else -1, 0)
            letter_parity = 0
        if parity:
            letter_exponent = multiply_by_q(letter_exponent)
        exponent = add(exponent, letter_exponent)
        parity ^= letter_parity
    return exponent, parity


def main():
    e, u = (1,), (2,)
    h = product(u, e, inverse(u))
    a = product(e, h, e)
    x = product(a, power(u, 2))
    c = product(power(u, 2), a, power(u, 2))
    f = product(inverse(x), h, x)
    d = product(e, inverse(a), f)
    s = product(f, a, f)
    rho = product(inverse(x), inverse(s), inverse(c))
    b = product(rho, inverse(u), rho)

    rel_c = power(c, 2)
    rel_rho = product(power(rho, 2), inverse(e), inverse(u))
    rel_b = product(b, x, inverse(u), inverse(d))
    rel_a = product(a, c, d, b)

    assert normal_form(rel_c) == ((4, 4), 0)
    assert normal_form(rel_rho) == ((-6, -7), 1)
    assert normal_form(rel_b) == ((-3, -9), 0)
    assert normal_form(rel_a) == ((-9, 0), 1)
    assert normal_form(power(u, 8)) == ((8, 0), 0)

    # Q=R_rho R_a^-1 has exponent 3-7q and no terminal e.
    q_word = product(rel_rho, inverse(rel_a))
    q_exponent, q_parity = normal_form(q_word)
    assert (q_exponent, q_parity) == ((3, -7), 0)

    # If P has exponent -3-9q and Q has exponent 3-7q, then
    # -P + qP - 2qQ = 8 in Z[q]/(q^2-1).
    p_exponent = (-3, -9)
    left = add(
        (-p_exponent[0], -p_exponent[1]),
        add(
            multiply_by_q(p_exponent),
            tuple(-2 * value for value in multiply_by_q(q_exponent)),
        ),
    )
    assert left == (8, 0)
    print("all cyclic-normalizer Titz gate checks passed")


if __name__ == "__main__":
    main()
