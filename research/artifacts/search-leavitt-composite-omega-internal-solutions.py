#!/usr/bin/env python3
"""Exact bounded internal-solution search for the composite-Omega word.

Elements of ``L_F2(1,2)`` are XOR-sets of monomials ``s_u t_v`` in Bergman
normal form.  The standard 20-leaf prefix chart embeds ``M_20(L)`` back into
``L``, so equality of the resulting units is exact.  No finite quotient or
finite truncation is used.
"""

import argparse
from itertools import product


def xor(*sets):
    out = set()
    for values in sets:
        out.symmetric_difference_update(values)
    return out


def canon(terms):
    def monomial(u, v):
        if u and v and u[-1] == "1" and v[-1] == "1":
            return xor(monomial(u[:-1], v[:-1]),
                       monomial(u[:-1] + "0", v[:-1] + "0"))
        return {(u, v)}

    out = set()
    for u, v in terms:
        out.symmetric_difference_update(monomial(u, v))
    return frozenset(out)


def mul_monomial(left, right):
    u, v = left
    x, y = right
    if x.startswith(v):
        return u + x[len(v):], y
    if v.startswith(x):
        return u, y + v[len(x):]
    return None


def mul(left, right):
    out = set()
    for first in left:
        for second in right:
            term = mul_monomial(first, second)
            if term is not None:
                if term in out:
                    out.remove(term)
                else:
                    out.add(term)
    return canon(out)


ONE = canon({("", "")})
S0 = canon({("0", "")})
S1 = canon({("1", "")})
T0 = canon({("", "0")})
T1 = canon({("", "1")})


def prefix(index):
    return "1" * (index - 1) + "0" if index < 20 else "1" * 19


def root(row, coefficient, column):
    out = set(ONE)
    for u, v in coefficient:
        out.symmetric_difference_update(canon({
            (prefix(row) + u, prefix(column) + v)
        }))
    return canon(out)


def cycle():
    return canon({(prefix(index % 20 + 1), prefix(index))
                  for index in range(1, 21)})


def power(unit, exponent):
    result = ONE
    for _ in range(exponent):
        result = mul(result, unit)
    return result


A = root(1, S0, 2)
E = root(1, T1, 2)
Q = mul(root(3, S1, 4), root(11, T0, 12))
P = cycle()
PINV = power(P, 19)
R = mul(Q, P)
RINV = mul(PINV, Q)
C = root(1, S0, 3)
B = mul(mul(mul(mul(R, R), A), RINV), RINV)
D = mul(mul(mul(mul(P, P), C), PINV), PINV)

UNITS = {
    "p": P, "P": PINV, "q": Q, "r": R, "R": RINV,
    "a": A, "e": E, "c": C, "b": B, "d": D,
}
INVERSE = {
    "p": "P", "P": "p", "q": "q", "r": "R", "R": "r",
    "a": "a", "e": "e", "c": "c", "b": "b", "d": "d",
}
ALPHABET = tuple(UNITS)


def inverse_word(word):
    return tuple(INVERSE[letter] for letter in reversed(word))


def evaluate(word):
    result = ONE
    for letter in word:
        result = mul(result, UNITS[letter])
    return result


def composite_word(t):
    # W'=r t e t a t^-1 c t^2 b t^-1 d t p t.
    tinv = inverse_word(t)
    return (("r",) + t + ("e",) + t + ("a",) + tinv + ("c",)
            + t + t + ("b",) + tinv + ("d",) + t + ("p",) + t)


def reduced_words(length):
    if length == 0:
        yield ()
        return
    for word in product(ALPHABET, repeat=length):
        if all(INVERSE[word[index]] != word[index + 1]
               for index in range(length - 1)):
            yield word


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=4)
    args = parser.parse_args()

    assert mul(Q, Q) == ONE
    assert power(P, 20) == ONE
    assert mul(B, B) == ONE and mul(D, D) == ONE

    tested = 0
    solutions = []
    for length in range(args.radius + 1):
        for candidate in reduced_words(length):
            tested += 1
            if evaluate(composite_word(candidate)) == ONE:
                solutions.append(candidate)
                print("SOLUTION", " ".join(candidate) or "1", flush=True)
        print(f"radius {length}: tested {tested}, solutions {len(solutions)}",
              flush=True)

    print(f"DONE tested={tested} solutions={len(solutions)}")


if __name__ == "__main__":
    main()
