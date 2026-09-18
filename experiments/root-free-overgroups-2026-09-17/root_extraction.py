#!/usr/bin/env python3
"""Certificate check for sl-r-polynomial-has-no-root-free-laurent-overgroup
(and hence kt-compressor-stable-kernel-overgroups-are-polynomial).

Claim tested: if h in SL_r(R), R = F_p[x_1^(+-1),...,x_d^(+-1)], r >= 3, has an
entry outside A = F_p[x_1,...,x_d], then an explicit word in h, h^(-1) and
elements of SL_r(A) evaluates to a root element e_ab(f) with f not in A.

The word is the one built in the proof
(research/sl-r-polynomial-no-root-free-laurent-overgroup-proof.md):
  tau = h e_ij(1) h^-1, gamma-normalisation of the row w, the double commutator
  Y = [e_nk(1), [tau, 1 + v e_k^T]] = 1 + u_k w_n v e_k^T, and the column lemma
  [e_cb(1), Y] = e_ck(y_b).
Every product is evaluated as an actual matrix product, and the result is
checked to be the identity plus one non-polynomial off-diagonal entry.
Also checks the two commutator identities on random data.

Run:  python3 root_extraction.py   (stdlib only; prints PASS lines, exits 1 on failure)
"""
import random
import sys
from itertools import product

P = 2  # characteristic; rerun with P=3 below


class L:
    """Laurent polynomial over F_P: dict exponent-tuple -> nonzero coefficient."""
    __slots__ = ("t",)

    def __init__(self, t=None):
        self.t = {k: v % P for k, v in (t or {}).items() if v % P}

    @staticmethod
    def c(a, d):
        return L({(0,) * d: a})

    @staticmethod
    def mono(e, a=1):
        return L({tuple(e): a})

    def __add__(s, o):
        t = dict(s.t)
        for k, v in o.t.items():
            t[k] = (t.get(k, 0) + v) % P
        return L(t)

    def __neg__(s):
        return L({k: -v for k, v in s.t.items()})

    def __sub__(s, o):
        return s + (-o)

    def __mul__(s, o):
        t = {}
        for k1, v1 in s.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                t[k] = (t.get(k, 0) + v1 * v2) % P
        return L(t)

    def iszero(s):
        return not s.t

    def val(s, i):  # x_i-adic valuation (min exponent of x_i); +inf for 0
        return min(k[i] for k in s.t) if s.t else 10 ** 9

    def ispoly(s):
        return all(min(k) >= 0 for k in s.t)

    def __eq__(s, o):
        return (s - o).iszero()

    def __repr__(s):
        return " + ".join(f"{v}*x^{k}" for k, v in sorted(s.t.items())) or "0"


def I(r, d):
    return [[L.c(1 if a == b else 0, d) for b in range(r)] for a in range(r)]


def mul(X, Y):
    r = len(X)
    d = D
    Z = [[L.c(0, d) for _ in range(r)] for _ in range(r)]
    for a in range(r):
        for c in range(r):
            if X[a][c].iszero():
                continue
            for b in range(r):
                if not Y[c][b].iszero():
                    Z[a][b] = Z[a][b] + X[a][c] * Y[c][b]
    return Z


def elem(r, a, b, f):
    X = I(r, D)
    X[a][b] = X[a][b] + f
    return X


def outer(u, w):  # column u, row w
    return [[ui * wj for wj in w] for ui in u]


def add(X, Y):
    return [[a + b for a, b in zip(r1, r2)] for r1, r2 in zip(X, Y)]


def scal(c, X):
    return [[c * a for a in row] for row in X]


def eq(X, Y):
    return all(a == b for r1, r2 in zip(X, Y) for a, b in zip(r1, r2))


class G:
    """Group element with its inverse and a flag 'in SL_r(A)' for bookkeeping."""

    def __init__(self, M, Mi, poly, name):
        self.M, self.Mi, self.poly, self.name = M, Mi, poly, name

    def __mul__(s, o):
        return G(mul(s.M, o.M), mul(o.Mi, s.Mi), s.poly and o.poly, f"({s.name}*{o.name})")

    def inv(s):
        return G(s.Mi, s.M, s.poly, f"{s.name}^-1")


def E(r, a, b, f):
    assert f.ispoly()
    return G(elem(r, a, b, f), elem(r, a, b, -f), True, f"e{a}{b}")


def transv(v, phi):
    """1 + v phi with polynomial v, phi and phi v = 0: an element of SL_r(A)."""
    r = len(v)
    s = L.c(0, D)
    for a in range(r):
        s = s + phi[a] * v[a]
    assert s.iszero() and all(x.ispoly() for x in v + phi)
    return G(add(I(r, D), outer(v, phi)), add(I(r, D), scal(L.c(-1, D), outer(v, phi))), True, "T")


def comm(a, b):
    return a * b * a.inv() * b.inv()


def is_root(X):
    """Return (a,b,f) if X = 1 + f e_ab with a != b, else None."""
    r = len(X)
    off = []
    for a in range(r):
        for b in range(r):
            want = L.c(1 if a == b else 0, D)
            if not (X[a][b] == want):
                if a == b:
                    return None
                off.append((a, b, X[a][b]))
    return off[0] if len(off) == 1 else None


def extract(h, r):
    """Word in h, h^-1, SL_r(A) giving a non-polynomial root, following the proof."""
    for i, j, pi in product(range(r), range(r), range(D)):
        if i == j:
            continue
        tau = h * E(r, i, j, L.c(1, D)) * h.inv()
        u = [h.M[l][i] for l in range(r)]
        w = [h.Mi[j][n] for n in range(r)]
        N = outer(u, w)
        if all(N[a][b].val(pi) >= 0 for a in range(r) for b in range(r)):
            continue
        # gamma-normalisation: make every coordinate of w pi-minimal
        m = min(x.val(pi) for x in w)
        a0 = next(a for a in range(r) if w[a].val(pi) == m)
        gam = G(I(r, D), I(r, D), True, "1")
        for a in range(r):
            if a != a0 and w[a].val(pi) > m:
                gam = gam * E(r, a0, a, L.c(-1, D))  # w gamma^-1 adds w_a0 to w_a
        tau1 = gam * tau * gam.inv()
        return finish(tau1, gam, u, w, pi, r, tau)
    return None


def uw_of(t, g, u, w):
    u2 = [sum((g.M[a][c] * u[c] for c in range(len(u))), L.c(0, D)) for a in range(len(u))]
    w2 = [sum((w[c] * g.Mi[c][b] for c in range(len(w))), L.c(0, D)) for b in range(len(w))]
    return u2, w2


def finish(tau1, gam, u, w, pi, r, tau):
    u1, w1 = uw_of(tau1, gam, u, w)
    N1 = outer(u1, w1)
    m = min(x.val(pi) for x in w1)
    assert all(x.val(pi) == m for x in w1)
    bad = [(k, n) for k in range(r) for n in range(r) if k != n and N1[k][n].val(pi) < 0]
    if not bad:  # diagonal case: provably unreachable (proof Step 4 remark); kept as a guard
        k = next(k for k in range(r) if N1[k][k].val(pi) < 0)
        n = (k + 1) % r
        g = E(r, k, n, L.c(1, D))
        tau1 = g * tau1 * g.inv()
        u1, w1 = uw_of(tau1, g, u1, w1)
        N1 = outer(u1, w1)
        assert N1[k][n].val(pi) < 0, "diagonal step failed"
        bad = [(k, n)]
    k, n = bad[0]
    # q = mu w1, with mu the monomial clearing all x_i-valuations of w1
    mins = [min(x.val(i) for x in w1) for i in range(D)]
    mu = L.mono([-e for e in mins])
    q = [mu * x for x in w1]
    assert all(x.ispoly() for x in q)
    a = next(a for a in range(r) if a != k and q[a].val(pi) == 0)
    b = next(b for b in range(r) if b not in (a, k))
    v = [L.c(0, D) for _ in range(r)]
    v[a], v[b] = q[b], -q[a]
    ek = [L.c(1 if c == k else 0, D) for c in range(r)]
    X1 = comm(tau1, transv(v, ek))
    Y = comm(E(r, n, k, L.c(1, D)), X1)
    # Y = 1 + u_k w_n v e_k^T
    pred = add(I(r, D), outer([u1[k] * w1[n] * x for x in v], ek))
    assert eq(Y.M, pred), "double commutator identity failed"
    c = next(c for c in range(r) if c not in (k, b))
    root = comm(E(r, c, b, L.c(1, D)), Y)
    got = is_root(root.M)
    assert got is not None, "column lemma failed"
    assert got[0] == c and got[1] == k and not got[2].ispoly(), got
    return got, root


def random_h(r, nsteps, rng):
    h = G(I(r, D), I(r, D), True, "1")
    for _ in range(nsteps):
        a, b = rng.sample(range(r), 2)
        e = [rng.choice([-1, 0, 0, 1]) for _ in range(D)]
        f = L.mono(e, rng.randrange(1, P))
        h = h * G(elem(r, a, b, f), elem(r, a, b, -f), f.ispoly(), "x")
    return h


def check_identities(r, rng, trials=30):
    for _ in range(trials):
        h = random_h(r, 4, rng)
        i, j = rng.sample(range(r), 2)
        u = [h.M[l][i] for l in range(r)]
        w = [h.Mi[j][n] for n in range(r)]
        tau = G(add(I(r, D), outer(u, w)), add(I(r, D), scal(L.c(-1, D), outer(u, w))), False, "tau")
        mins = [min(x.val(t) for x in w) for t in range(D)]
        q = [L.mono([-e for e in mins]) * x for x in w]
        a, b, k = rng.sample(range(r), 3)
        v = [L.c(0, D) for _ in range(r)]
        v[a], v[b] = q[b], -q[a]
        ek = [L.c(1 if c == k else 0, D) for c in range(r)]
        X1 = comm(tau, transv(v, ek))
        pred1 = add(I(r, D), scal(L.c(-1, D) * u[k], outer(v, w)))
        assert eq(X1.M, pred1), "identity (1) failed"
    return True


if __name__ == "__main__":
    ok = True
    for P, D, r, n, steps in [(2, 2, 3, 25, 4), (2, 3, 3, 25, 4), (3, 3, 3, 20, 4), (2, 3, 4, 15, 5), (3, 2, 4, 15, 5)]:
        globals()["P"], globals()["D"] = P, D
        rng = random.Random(1000 * P + 10 * D + r)
        check_identities(r, rng)
        done = 0
        for _ in range(n):
            h = random_h(r, steps, rng)
            nonpoly = any(not h.M[a][b].ispoly() for a in range(r) for b in range(r))
            res = extract(h, r)
            if nonpoly:
                assert res is not None, "no extraction for a non-polynomial h"
                done += 1
            else:
                assert res is None
        print(f"PASS p={P} d={D} r={r}: identities ok; {done} non-polynomial h, each yields an explicit non-polynomial root")
    sys.exit(0)
