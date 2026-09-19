#!/usr/bin/env python3
"""Sanity checks for leavitt-nonnegative-part-is-matrix-union-over-free-algebra (over F_2).

Model: L_k(1,2) acts on k[N] by s_i e_n = e_{2n+i}, t_i e_n = e_{(n-i)/2} (n = i mod 2).
Elements are represented as sparse maps {n: set of m} over F_2 (sets of indices, XOR sum),
evaluated on basis vectors e_n for n < BOUND.

Checks:
  1. Relations t_i s_j = delta_ij and s_0 t_0 + s_1 t_1 = 1.
  2. s_w e_1 are distinct for all words of length <= 10 (free algebra embeds).
  3. Block identity s_u p t_v = sum_{x,y} s_{uy} d_y(p x_x) t_{vx} for random u, v, p.
  4. Phi_N is multiplicative on random matrices, for N = 1, 2.
"""
import itertools
import random

BOUND = 600


def s(i):
    return lambda n: {2 * n + i}


def t(i):
    return lambda n: {(n - i) // 2} if n % 2 == i and n >= i else set()


def apply(ops_word, n):
    """Apply a product op_1 op_2 ... op_k (rightmost first) to e_n; returns set (F_2 vector)."""
    vec = {n}
    for op in reversed(ops_word):
        new = set()
        for m in vec:
            new ^= op(m)
        vec = new
    return vec


def elt_apply(elt, n):
    """elt: list of words (each word a list of ops); F_2 sum."""
    out = set()
    for w in elt:
        out ^= apply(w, n)
    return out


def sw(word):
    return [s(int(c)) for c in word]


def tw(word):
    return [t(int(c)) for c in reversed(word)]


def equal(e1, e2):
    return all(elt_apply(e1, n) == elt_apply(e2, n) for n in range(BOUND))


def check_relations():
    for i in range(2):
        for j in range(2):
            lhs = [[t(i), s(j)]]
            rhs = [[]] if i == j else []
            assert equal(lhs, rhs)
    assert equal([[s(0), t(0)], [s(1), t(1)]], [[]])


def check_free():
    seen = {}
    for l in range(11):
        for w in itertools.product("01", repeat=l):
            m = apply(sw("".join(w)), 1)
            assert len(m) == 1
            m = next(iter(m))
            assert m not in seen, (w, seen[m])
            seen[m] = w


def rand_poly(rng, terms=3, maxlen=3):
    return [
        "".join(rng.choice("01") for _ in range(rng.randint(0, maxlen)))
        for _ in range(terms)
    ]


def left_quot(y, w):
    return w[1:] if w and w[0] == y else None


def check_block(rng):
    for _ in range(40):
        N = rng.randint(0, 2)
        u = "".join(rng.choice("01") for _ in range(N))
        v = "".join(rng.choice("01") for _ in range(N))
        p = rand_poly(rng)
        lhs = [sw(u) + sw(w) + tw(v) for w in p]
        rhs = []
        for x in "01":
            for y in "01":
                for w in p:
                    q = left_quot(y, w + x)
                    if q is not None:
                        rhs.append(sw(u + y) + sw(q) + tw(v + x))
        assert equal(lhs, rhs), (u, v, p)


def phi(N, mat):
    words = ["".join(w) for w in itertools.product("01", repeat=N)]
    out = []
    for a, u in enumerate(words):
        for b, v in enumerate(words):
            for w in mat[a][b]:
                out.append(sw(u) + sw(w) + tw(v))
    return out


def matmul(A, B):
    n = len(A)
    C = [[[] for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for w1 in A[i][k]:
                    for w2 in B[k][j]:
                        C[i][j].append(w1 + w2)
    return C


def check_phi_mult(rng):
    for N in (1, 2):
        n = 2 ** N
        for _ in range(5):
            A = [[rand_poly(rng, 1, 2) for _ in range(n)] for _ in range(n)]
            B = [[rand_poly(rng, 1, 2) for _ in range(n)] for _ in range(n)]
            prod = [w1 + w2 for w1 in phi(N, A) for w2 in phi(N, B)]
            assert equal(prod, phi(N, matmul(A, B)))


if __name__ == "__main__":
    rng = random.Random(20260919)
    check_relations()
    check_free()
    check_block(rng)
    check_phi_mult(rng)
    print("all checks passed")
