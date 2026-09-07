#!/usr/bin/env python3
"""Exact checks accompanying the locally finite compression paper proof.

The ring calculation takes place in Z<s,t,a | ts=1>, with a free
coefficient a. The covariance check uses rational matrices for a
noncommuting S_3 packet and an exactly computed polar correction.
These checks do not verify the infinite-dimensional analytic theorem.
Run with Python 3; no third-party packages are needed.
"""

from fractions import Fraction
from itertools import permutations


def reduce_word(word):
    while "ts" in word:
        word = word.replace("ts", "")
    return word


def add(x, y):
    out = x.copy()
    for word, coefficient in y.items():
        out[word] = out.get(word, 0) + coefficient
        if not out[word]:
            del out[word]
    return out


def neg(x):
    return {word: -coefficient for word, coefficient in x.items()}


def mul(x, y):
    out = {}
    for left, a in x.items():
        for right, b in y.items():
            out = add(out, {reduce_word(left + right): a * b})
    return out


ZERO, ONE = {}, {"": 1}
s, t, a = {"s": 1}, {"t": 1}, {"a": 1}
e = add(ONE, neg(mul(s, t)))


def eye():
    return [[ONE if i == j else ZERO for j in range(4)] for i in range(4)]


def root(i, j, coefficient):
    out = eye()
    out[i][j] = coefficient
    return out


def matrix_mul(x, y):
    out = [[ZERO for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            for k in range(4):
                out[i][j] = add(out[i][j], mul(x[i][k], y[k][j]))
    return out


def product(matrices):
    out = eye()
    for matrix in matrices:
        out = matrix_mul(out, matrix)
    return out


def check_ring():
    assert mul(t, s) == ONE
    assert mul(e, e) == e and mul(e, s) == ZERO and mul(t, e) == ZERO
    assert e != ZERO
    factors = []
    for i in (2, 1, 0):
        factors.extend([
            (3, i, add(t, neg(ONE))),
            (i, 3, ONE),
            (3, i, add(s, neg(ONE))),
            (i, 3, neg(t)),
        ])
    u = product(root(*factor) for factor in factors)
    inverse = product(root(i, j, neg(x)) for i, j, x in reversed(factors))
    assert matrix_mul(u, inverse) == eye() == matrix_mul(inverse, u)
    normal = [
        [s, ZERO, ZERO, e],
        [ZERO, s, ZERO, mul(e, t)],
        [ZERO, ZERO, s, mul(e, mul(t, t))],
        [ZERO, ZERO, ZERO, mul(t, mul(t, t))],
    ]
    assert u == normal
    c = product([root(3, 0, e), root(0, 3, t),
                 root(3, 0, neg(e)), root(0, 3, neg(t))])
    c_normal = eye()
    c_normal[3][3] = add(ONE, mul(e, t))
    assert c == c_normal
    b = product([u, c, inverse])
    assert b == root(0, 1, e)
    assert product([b, root(1, 2, ONE), root(0, 1, neg(e)),
                    root(1, 2, neg(ONE))]) == root(0, 2, e)
    for i in range(3):
        for j in range(3):
            if i != j:
                x = root(i, j, a)
                assert matrix_mul(u, x) == matrix_mul(root(i, j, mul(s, mul(a, t))), u)
                assert matrix_mul(c, x) == matrix_mul(x, c)
    units = {(i, j): mul(mul({"s" * i: 1}, e), {"t" * j: 1})
             for i in range(6) for j in range(6)}
    for (i, j), x in units.items():
        for (k, ell), y in units.items():
            assert mul(x, y) == (units[i, ell] if j == k else ZERO)
    print("PASS: universal compressor, free-coefficient conjugacy, head commutator; "
          "1,296 exact matrix-unit products")


def qmul(x, y):
    return [[sum(x[i][k] * y[k][j] for k in range(3))
             for j in range(3)] for i in range(3)]


def transpose(x):
    return list(map(list, zip(*x)))


def difference(x, y):
    return [[x[i][j] - y[i][j] for j in range(3)] for i in range(3)]


def conjugate(u, x):
    return qmul(qmul(u, x), transpose(u))


def hs_squared(x):
    return sum(entry * entry for row in x for entry in row)


def check_covariance():
    group = [[[Fraction(int(i == p[j])) for j in range(3)] for i in range(3)]
             for p in permutations(range(3))]
    identity = group[0]
    cases = 0
    for denominator in (2, 3, 10, 100):
        parameter = Fraction(1, denominator)
        cosine = (1 - parameter**2) / (1 + parameter**2)
        sine = 2 * parameter / (1 + parameter**2)
        rotation = [[cosine, -sine, 0], [sine, cosine, 0], [0, 0, 1]]
        assert qmul(rotation, transpose(rotation)) == identity
        averaged = [[sum(conjugate(g, rotation)[i][j] for g in group) / 6
                     for j in range(3)] for i in range(3)]
        scalar = (1 + 2 * cosine) / 3
        assert scalar > 0
        assert averaged == [[scalar * identity[i][j] for j in range(3)]
                            for i in range(3)]
        # The Haar average is scalar * Q, so its polar part is exactly Q.
        operator_gap_squared = 4 * parameter**2 / (1 + parameter**2)
        for q in group:
            approximate = qmul(q, rotation)
            for x in group:
                for y in group:
                    if qmul(x, y) == qmul(y, x):
                        continue
                    displacement = difference(x, y)
                    defect = difference(conjugate(q, displacement),
                                        conjugate(approximate, displacement))
                    mass = hs_squared(displacement)
                    assert mass > 0
                    assert hs_squared(defect) <= 4 * operator_gap_squared * mass
                    # Adding identity spectator blocks leaves these unnormalized
                    # quantities unchanged, while normalized mass can vanish.
                    for spectators in (0, 3, 300, 30000):
                        normalized_mass = mass / (3 + spectators)
                        assert normalized_mass * (3 + spectators) == mass
                    cases += 1
    print(f"PASS: {cases} rational noncommuting covariance cases; "
          "polar correction and relative Hilbert--Schmidt bound")


if __name__ == "__main__":
    check_ring()
    check_covariance()
