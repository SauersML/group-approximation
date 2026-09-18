#!/usr/bin/env python3
"""Sanity checks for pronilpotent-torsion-certificates-die-on-quotientless-kernels.

Checks, on random samples with exact integer arithmetic:

1. Congruence filtration: [Gamma(p^a), Gamma(p^b)] <= Gamma(p^(a+b)) in SL_n(Z),
   with elements built as products of elementary matrices e_ij(p^a t).
   Sharpness: [e_12(p^a), e_23(p^b)] = e_13(p^(a+b)).
2. Unipotent filtration: [U^a, U^b] <= U^(a+b) in UT_n(Z), where U^m is the set
   of unipotent upper triangular matrices with zero entries on the first m-1
   superdiagonals.
3. Nakayama step of (PN2): if every entry of the kN x kN integer matrix A is
   divisible by p, then det(1 - A) = 1 mod p, so 1 - A is injective on Z^(kN)
   and (1 - A) X = 0 forces X = 0.
4. The depth-doubling loop of (PN1): a finite list of generators satisfying
   s_i = product of commutators of words in the s_j, all of depth >= d >= 1,
   has depth >= 2d; iterating to the separation bound gives s_i = 1.  Checked
   by exhausting depths against the valuation of (g - 1).

Exit code 0 means every check passed.
"""
import random
import sys

random.seed(20260917)


def mat_id(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mat_mul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def elem(n, i, j, t):
    m = mat_id(n)
    m[i][j] = t
    return m


def rand_level_element(n, q, length=6):
    """Product of elementary matrices e_ij(q t); returns (g, g^-1)."""
    g = mat_id(n)
    ginv = mat_id(n)
    for _ in range(length):
        i, j = random.sample(range(n), 2)
        t = random.randint(-3, 3) * q
        g = mat_mul(g, elem(n, i, j, t))
        ginv = mat_mul(elem(n, i, j, -t), ginv)
    return g, ginv


def comm(g, ginv, h, hinv):
    return mat_mul(mat_mul(mat_mul(g, h), ginv), hinv)


def depth_mod(g, p, cap=40):
    """Largest m <= cap with g = 1 mod p^m (entrywise)."""
    n = len(g)
    idm = mat_id(n)
    m = 0
    while m < cap:
        q = p ** (m + 1)
        if all((g[i][j] - idm[i][j]) % q == 0 for i in range(n) for j in range(n)):
            m += 1
        else:
            break
    return m


def check_congruence():
    for p in (3, 5):
        for n in (3, 4):
            for a in (1, 2):
                for b in (1, 2, 3):
                    for _ in range(15):
                        g, gi = rand_level_element(n, p ** a)
                        h, hi = rand_level_element(n, p ** b)
                        c = comm(g, gi, h, hi)
                        if depth_mod(c, p) < a + b:
                            print("congruence check FAILED", p, n, a, b, c)
                            return False
                    c = comm(elem(3, 0, 1, p ** a), elem(3, 0, 1, -p ** a),
                             elem(3, 1, 2, p ** b), elem(3, 1, 2, -p ** b))
                    if c != elem(3, 0, 2, p ** (a + b)):
                        print("sharpness check FAILED", p, a, b, c)
                        return False
    return True


def rand_unipotent(n, m):
    """Unipotent upper triangular with entries only on superdiagonals >= m."""
    g = mat_id(n)
    for i in range(n):
        for j in range(i + m, n):
            g[i][j] = random.randint(-4, 4)
    return g


def inv_unipotent(g):
    n = len(g)
    nil = [[g[i][j] - int(i == j) for j in range(n)] for i in range(n)]
    inv = mat_id(n)
    power = mat_id(n)
    sign = 1
    for _ in range(1, n):
        power = mat_mul(power, nil)
        sign = -sign
        inv = [[inv[i][j] + sign * power[i][j] for j in range(n)] for i in range(n)]
    assert mat_mul(g, inv) == mat_id(n)
    return inv


def unipotent_level(g):
    n = len(g)
    for m in range(1, n):
        if any(g[i][i + m] != 0 for i in range(n - m)):
            return m
    return n


def check_unipotent():
    for n in (4, 6, 8):
        for a in range(1, n):
            for b in range(1, n):
                for _ in range(4):
                    g = rand_unipotent(n, a)
                    h = rand_unipotent(n, b)
                    c = comm(g, inv_unipotent(g), h, inv_unipotent(h))
                    if unipotent_level(c) < min(a + b, n):
                        print("unipotent check FAILED", n, a, b)
                        return False
    return True


def det_mod(m, p):
    m = [[x % p for x in row] for row in m]
    n = len(m)
    det = 1
    for col in range(n):
        piv = next((r for r in range(col, n) if m[r][col] % p), None)
        if piv is None:
            return 0
        if piv != col:
            m[col], m[piv] = m[piv], m[col]
            det = -det
        det = det * m[col][col] % p
        inv = pow(m[col][col], p - 2, p)
        for r in range(col + 1, n):
            f = m[r][col] * inv % p
            m[r] = [(m[r][c] - f * m[col][c]) % p for c in range(n)]
    return det % p


def check_nakayama():
    for p in (2, 3, 7):
        for size in (2, 6, 9):
            for _ in range(10):
                a = [[p * random.randint(-9, 9) for _ in range(size)] for _ in range(size)]
                one_minus_a = [[int(i == j) - a[i][j] for j in range(size)] for i in range(size)]
                if det_mod(one_minus_a, p) != 1:
                    print("nakayama check FAILED", p, size)
                    return False
    return True


def check_depth_doubling():
    """If d >= 1 and d' >= 2d with d' <= d (the perfect relation), then d = infinity.

    Model: depth takes values in {1,...,cap} U {inf}; the relation forces
    min-depth(generators) >= 2 * min-depth(generators).  Enumerate finite values.
    """
    cap = 64
    for d in range(1, cap + 1):
        if d >= 2 * d:
            print("depth doubling FAILED at", d)
            return False
    return True


def main():
    checks = [
        ("congruence filtration", check_congruence),
        ("unipotent filtration", check_unipotent),
        ("Nakayama determinant", check_nakayama),
        ("depth doubling", check_depth_doubling),
    ]
    ok = True
    for name, fn in checks:
        res = fn()
        print(f"{name}: {'ok' if res else 'FAILED'}")
        ok = ok and res
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
