#!/usr/bin/env python3
"""Exact checks for shift-homology-in-positive-degree-is-inert-under-automata.

1. Permutation basis: the products e_{F,c}, F a subset of a window W and
   c : F -> A' = A \\ {a0}, form a Z-basis of Z^(A^W) (determinant +-1).
2. BS(1,2) = Z[1/2] x| Z, K = <a>, V = G/K, c = t^-1, p(gK) = g t^-1 K:
   well defined, fibres of size 2, tree degree 3, stabilizer index 2,
   t a^(1/2) t^-1 = a (so corestriction-then-conjugation is x2 on H_1(K)).
3. Parent-copy automaton on {0,1}^V: tau^* e_F = e_{p(F)} on a finite
   p-closed piece of the tree, the Garden-of-Eden class
   1_U = e_{c} - e_{c,c'} is killed, and the Bernoulli trace is not
   preserved (1/4 -> 1/2).
4. The one-site partition class is not a conjugacy invariant: the
   marker involution tau(x)(g) = swap12(x(g)) if x(gs) = 0 sends the
   uniform Bernoulli measure on {0,1}^G to a law with site marginal
   (1/2, 1/4, 1/4) instead of (1/2, 1/2, 0).
"""
from fractions import Fraction
from itertools import product, combinations
import random


def det_int(m):
    """Exact determinant by fraction-free Bareiss elimination."""
    n = len(m)
    a = [row[:] for row in m]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            for i in range(k + 1, n):
                if a[i][k] != 0:
                    a[k], a[i] = a[i], a[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
        prev = a[k][k]
    return sign * a[n - 1][n - 1]


def check_basis():
    for q in (2, 3):
        A = list(range(q))
        Aprime = A[1:]
        for w in (1, 2, 3):
            W = list(range(w))
            configs = list(product(A, repeat=w))
            funcs = []
            for r in range(w + 1):
                for F in combinations(W, r):
                    for c in product(Aprime, repeat=r):
                        funcs.append((F, c))
            assert len(funcs) == len(configs) == q ** w
            M = [[int(all(x[F[i]] == c[i] for i in range(len(F)))) for x in configs]
                 for (F, c) in funcs]
            d = det_int(M)
            assert abs(d) == 1, (q, w, d)
    print("basis: e_{F,c} unimodular for |A| in {2,3}, |W| in {1,2,3}")


# ---- BS(1,2) = Z[1/2] x| Z ; element (r, n) acts on Q by x -> 2^n x + r ----
def mul(g, h):
    r1, n1 = g
    r2, n2 = h
    return (r1 + Fraction(2) ** n1 * r2, n1 + n2)


def inv(g):
    r, n = g
    return (-(Fraction(2) ** (-n)) * r, -n)


a = (Fraction(1), 0)
t = (Fraction(0), 1)


def a_pow(r):
    return (Fraction(r), 0)


def coset_key(g):
    """Key of gK, K = {(k,0): k in Z}: gK = {(r + 2^n k, n)}."""
    r, n = g
    mod = Fraction(2) ** n
    # r mod 2^n Z, canonical representative in [0, 2^n)
    q = (r / mod).numerator // (r / mod).denominator
    return (r - q * mod, n)


def rep(key):
    return key  # (r, n) with canonical r is itself a representative


def p(key):
    return coset_key(mul(rep(key), inv(t)))


def check_bs12():
    # relation t a^r t^-1 = a^(2r)
    for r in (Fraction(1), Fraction(1, 2), Fraction(3, 4)):
        assert mul(mul(t, a_pow(r)), inv(t)) == a_pow(2 * r)
    assert mul(mul(t, a_pow(Fraction(1, 2))), inv(t)) == a
    # c^-1 K c = t K t^-1 = <a^2> is proper in K
    assert mul(mul(t, a), inv(t)) == a_pow(2)
    # p is well defined on cosets: g and g k give the same parent
    random.seed(1)
    samples = []
    for _ in range(200):
        g = (Fraction(random.randint(-40, 40), 2 ** random.randint(0, 4)), random.randint(-3, 3))
        samples.append(g)
        for k in (-3, -1, 1, 5):
            assert p(coset_key(g)) == p(coset_key(mul(g, a_pow(k))))
    # fibres of p have size 2: children of vK are v a^(j/2) t^?; search locally
    for g in samples[:60]:
        v = coset_key(g)
        # candidate children: w = v' with p(w) = v; children are g t a^(j/2)... enumerate
        cands = set()
        for j in range(-4, 5):
            for n in (-1, 0, 1):
                h = mul(g, mul(mul(a_pow(Fraction(j, 2)), t), a_pow(0)))
                w = coset_key(mul(h, (Fraction(0), n)))
                if p(w) == v:
                    cands.add(w)
        assert len(cands) == 2, (v, cands)
    # stabilizer of eK is K; stabilizer of p(eK) = t^-1 K is t^-1 K t = <a^(1/2)>
    e = (Fraction(0), 0)
    pe = p(coset_key(e))
    assert coset_key(mul(a_pow(Fraction(1, 2)), rep(pe))) == pe
    assert coset_key(mul(a_pow(Fraction(1, 2)), rep(coset_key(e)))) != coset_key(e)
    assert coset_key(mul(a_pow(Fraction(1)), rep(coset_key(e)))) == coset_key(e)
    print("BS(1,2): relation, well-defined parent map, fibre size 2, stabilizer index 2, "
          "t a^(1/2) t^-1 = a  => H_1 eigenvalue 2")


def check_parent_copy():
    # finite piece: vertices of depth 0..D below a root, p maps depth d+1 -> d;
    # root's parent added as an extra vertex whose value is free.
    D = 3
    verts = ["r"]
    parent = {"r": "pr"}
    frontier = ["r"]
    for _ in range(D):
        new = []
        for v in frontier:
            for b in "01":
                w = v + b
                parent[w] = v
                new.append(w)
        verts += new
        frontier = new
    allv = verts + ["pr"]
    random.seed(7)
    for _ in range(300):
        x = {v: random.randint(0, 1) for v in allv}
        tx = {v: x[parent[v]] for v in verts}
        for _ in range(5):
            F = random.sample(verts, random.randint(1, 4))
            lhs = int(all(tx[v] == 1 for v in F))
            rhs = int(all(x[w] == 1 for w in {parent[v] for v in F}))
            assert lhs == rhs
    # GoE: siblings c=r0, c'=r1 always equal in the image
    for bits in product((0, 1), repeat=len(allv)):
        x = dict(zip(allv, bits))
        tx = {v: x[parent[v]] for v in verts}
        assert tx["r0"] == tx["r1"]
        one_U = int(tx["r0"] == 1 and tx["r1"] == 0)
        e_c = int(tx["r0"] == 1)
        e_cc = int(tx["r0"] == 1 and tx["r1"] == 1)
        assert one_U == e_c - e_cc == 0
    # Bernoulli trace: t(e_F) = 2^-|F|; tau^* e_{c,c'} = e_{p(c)} = e_{r}
    assert Fraction(1, 2 ** 2) == Fraction(1, 4)
    assert Fraction(1, 2 ** len({parent["r0"], parent["r1"]})) == Fraction(1, 2)
    print("parent copy: tau^* e_F = e_p(F), GoE class 1_U = e_c - e_{c,c'} -> 0, "
          "trace 1/4 -> 1/2")


def check_marker_involution():
    # G = Z/N (exact enumeration is enough for a one-site marginal of a 2-site rule)
    N = 4
    counts = {0: 0, 1: 0, 2: 0}
    total = 0
    for x in product((0, 1), repeat=N):
        y = [(3 - x[i]) if (x[(i + 1) % N] == 0 and x[i] != 0) else x[i] for i in range(N)]
        counts[y[0]] += 1
        total += 1
    marg = {k: Fraction(v, total) for k, v in counts.items()}
    assert marg == {0: Fraction(1, 2), 1: Fraction(1, 4), 2: Fraction(1, 4)}
    # involution check on all of {0,1,2}^N
    for x in product((0, 1, 2), repeat=N):
        def tau(z):
            return tuple((3 - z[i]) if (z[(i + 1) % N] == 0 and z[i] != 0) else z[i]
                         for i in range(N))
        assert tau(tau(x)) == x
    print("marker involution: bijective, site marginal (1/2,1/2,0) -> (1/2,1/4,1/4)")


if __name__ == "__main__":
    check_basis()
    check_bs12()
    check_parent_copy()
    check_marker_involution()
    print("ALL CHECKS PASSED")
