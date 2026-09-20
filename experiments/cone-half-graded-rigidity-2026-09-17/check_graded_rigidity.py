#!/usr/bin/env python3
"""Sanity checks for cone-half-compressions-have-graded-rigid-commutants.

R = L_{F_2}(1,2), elements are sets of normal-form monomials (mu, nu) = s_mu t_nu over F_2
(symmetric difference = addition).  Normal form: no monomial with mu, nu both ending in 2
(replace s_{m2} t_{n2} = s_m t_n + s_{m1} t_{n1}).  deg(s_mu t_nu) = |mu| - |nu|.

Checks:
 (a) R_+ = span{s_mu, s_mu q} (q = s_1 t_1) is closed under multiplication up to a length bound,
     is spanned by homogeneous elements of degree |mu| >= 0, and dim (R_+)_j = 2^(j+1).
 (b) For random u in E_3(R_+) (products of elementary matrices x_ij(a), a in R_+), and random
     x in M_3(R_+): u^-1 has entries in R_+, u_0 (u^-1)_0 = 1, and the lowest-degree part of
     u x u^-1 is u_0 x_j (u^-1)_0 (the leading-term lemma, steps (i)-(ii) of the proof).
"""
import itertools
import random

random.seed(20260917)


def reduce_mono(m):
    mu, nu = m
    if mu and nu and mu[-1] == 2 and nu[-1] == 2:
        return add(reduce_mono((mu[:-1], nu[:-1])), reduce_mono((mu[:-1] + (1,), nu[:-1] + (1,))))
    return frozenset([m])


def add(a, b):
    return frozenset(set(a) ^ set(b))


def mono_mul(m1, m2):
    (mu, nu), (al, be) = m1, m2
    k = min(len(nu), len(al))
    if nu[:k] != al[:k]:
        return frozenset()
    if len(nu) <= len(al):
        return reduce_mono((mu + al[len(nu):], be))
    return reduce_mono((mu, be + nu[len(al):]))


def mul(a, b):
    out = frozenset()
    for m1 in a:
        for m2 in b:
            out = add(out, mono_mul(m1, m2))
    return out


ZERO = frozenset()
ONE = frozenset([((), ())])
Q = frozenset([((1,), (1,))])


def deg(m):
    return len(m[0]) - len(m[1])


def in_rplus_span(a):
    return all((nu == () ) or (nu == (1,) and mu and mu[-1] == 1) for (mu, nu) in a)


def rplus_basis(j):
    out = []
    for mu in itertools.product((1, 2), repeat=j):
        out.append(frozenset([(mu, ())]))
        out.append(frozenset([(mu + (1,), (1,))]))
    return out


def check_a(J=4):
    for j in range(J + 1):
        B = rplus_basis(j)
        monos = set().union(*B)
        assert len(monos) == 2 ** (j + 1), j
        assert all(deg(m) == j for m in monos)
    basis = [b for j in range(J + 1) for b in rplus_basis(j)]
    for a in basis:
        for b in basis:
            p = mul(a, b)
            assert in_rplus_span(p), (a, b, p)
            da = deg(next(iter(a)))
            db = deg(next(iter(b)))
            assert all(deg(m) == da + db for m in p)
    # generators close: q s_1 = s_1, q s_2 = 0, q q = q
    s1 = frozenset([((1,), ())]); s2 = frozenset([((2,), ())])
    assert mul(Q, s1) == s1 and mul(Q, s2) == ZERO and mul(Q, Q) == Q
    return len(basis)


# ---- matrices over R ----
N = 3


def mzero():
    return [[ZERO] * N for _ in range(N)]


def mid():
    M = mzero()
    for i in range(N):
        M[i][i] = ONE
    return M


def mmul(A, B):
    C = mzero()
    for i in range(N):
        for k in range(N):
            if not A[i][k]:
                continue
            for j in range(N):
                if B[k][j]:
                    C[i][j] = add(C[i][j], mul(A[i][k], B[k][j]))
    return C


def elem(i, j, a):
    M = mid()
    M[i][j] = a
    return M


def rand_rplus(maxlen=2, terms=2):
    a = ZERO
    for _ in range(terms):
        j = random.randint(0, maxlen)
        a = add(a, random.choice(rplus_basis(j)))
    return a


def part(M, d):
    return [[frozenset(m for m in M[i][j] if deg(m) == d) for j in range(N)] for i in range(N)]


def mindeg(M):
    ds = [deg(m) for i in range(N) for j in range(N) for m in M[i][j]]
    return min(ds) if ds else None


def check_b(trials=40):
    for _ in range(trials):
        u, v = mid(), mid()
        for _ in range(random.randint(1, 5)):
            i, j = random.sample(range(N), 2)
            a = rand_rplus()
            u = mmul(u, elem(i, j, a))
            v = mmul(elem(i, j, a), v)  # x_ij(a)^-1 = x_ij(a) in char 2
        assert mmul(u, v) == mid() and mmul(v, u) == mid()
        assert all(in_rplus_span(u[i][j]) and in_rplus_span(v[i][j]) for i in range(N) for j in range(N))
        u0, v0 = part(u, 0), part(v, 0)
        assert mmul(u0, v0) == mid()
        x = [[rand_rplus(3, 3) for _ in range(N)] for _ in range(N)]
        jx = mindeg(x)
        if jx is None:
            continue
        y = mmul(mmul(u, x), v)
        lead = mmul(mmul(u0, part(x, jx)), v0)
        assert mindeg(y) == jx
        assert part(y, jx) == lead
    return trials


if __name__ == "__main__":
    nb = check_a()
    print(f"(a) R_+ closure/grading: OK on {nb} basis elements, dims 2^(j+1) for j<=4")
    t = check_b()
    print(f"(b) leading-term lemma for u in E_3(R_+): OK on {t} random trials")
