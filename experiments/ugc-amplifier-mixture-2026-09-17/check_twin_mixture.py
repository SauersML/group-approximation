#!/usr/bin/env python3
"""Checks for twin-mixture-caps-deficit-ratio-of-local-amplifiers.

Exact (Fraction) brute force on tiny bipartite unique games.  A game is
(nL, nR, K, edges) with edges (u, v, perm, w) meaning label(v) = perm[label(u)].

Checks:
  1. value of a weighted disjoint union is the mass-weighted average;
  2. Theorem A on a concrete graph-massed component-local map, the 2-path
     game Phi: val Phi(M) = lam val Phi(S) + (1-lam) val Phi(H) and
     (1 - val Phi(N)) / (1 - val Phi(M)) <= (1 - val H) / (1 - val M);
  3. Theorem B ingredients: val(G x G') <= min(val G, val G'), the component
     decomposition of a tensor square of a disjoint union, and the product
     bound R' <= R/(1 - v0) on the resulting thresholds;
  4. the scalar inequality (1 - x^t)/(1 - y^t) <= (1 - x)/(1 - y), 0<=x<y<1.
Seed 20260918.  Exit code 0 iff every check passes.
"""
import itertools
import random
import sys
from fractions import Fraction as F

random.seed(20260918)
FAIL = []


def val(g):
    nL, nR, K, edges = g
    W = sum(e[3] for e in edges)
    byv = [[] for _ in range(nR)]
    for (u, v, p, w) in edges:
        byv[v].append((u, p, w))
    best = F(0)
    for lab in itertools.product(range(K), repeat=nL):
        tot = F(0)
        for v in range(nR):
            if not byv[v]:
                continue
            cnt = [F(0)] * K
            for (u, p, w) in byv[v]:
                cnt[p[lab[u]]] += w
            tot += max(cnt)
        if tot > best:
            best = tot
    return best / W


def mass(g):
    return sum(e[3] for e in g[3])


def union(*gs):
    """Disjoint union with absolute weights (all games share K)."""
    K = gs[0][2]
    oL = oR = 0
    edges = []
    for (nL, nR, k, es) in gs:
        assert k == K
        edges += [(u + oL, v + oR, p, w) for (u, v, p, w) in es]
        oL += nL
        oR += nR
    return (oL, oR, K, edges)


def scale(g, c):
    nL, nR, K, es = g
    return (nL, nR, K, [(u, v, p, w * c) for (u, v, p, w) in es])


def normalize(g):
    return scale(g, F(1) / mass(g))


def tensor(g, h):
    nL1, nR1, K1, e1 = g
    nL2, nR2, K2, e2 = h
    edges = []
    for (u1, v1, p1, w1) in e1:
        for (u2, v2, p2, w2) in e2:
            p = tuple(p1[a // K2] * K2 + p2[a % K2] for a in range(K1 * K2))
            edges.append((u1 * nL2 + u2, v1 * nR2 + v2, p, w1 * w2))
    return (nL1 * nL2, nR1 * nR2, K1 * K2, edges)


def inv(p):
    q = [0] * len(p)
    for i, x in enumerate(p):
        q[x] = i
    return tuple(q)


def two_path(g):
    """Phi(U): vertices = right side of U on both sides; for every left u and
    ordered pair of incident edges e=(u,v), f=(u,w'), the constraint
    label(w') = pi_f pi_e^{-1} label(v), weight w_e w_f / W_u.  Mass = mass(U),
    determined by the weighted graph only."""
    nL, nR, K, es = g
    inc = [[] for _ in range(nL)]
    for (u, v, p, w) in es:
        inc[u].append((v, p, w))
    edges = []
    for u in range(nL):
        Wu = sum(w for (_, _, w) in inc[u])
        for (v, pe, we) in inc[u]:
            pie = inv(pe)
            for (x, pf, wf) in inc[u]:
                comp = tuple(pf[pie[a]] for a in range(K))
                edges.append((v, x, comp, we * wf / Wu))
    return (nR, nR, K, edges)


def rand_graph(nL, nR, m):
    es = []
    for _ in range(m):
        es.append((random.randrange(nL), random.randrange(nR),
                   F(random.randint(1, 3))))
    return es


def shift(K, t):
    return tuple((a + t) % K for a in range(K))


def game_on(nL, nR, K, graph, perms):
    return (nL, nR, K, [(u, v, p, w) for (u, v, w), p in zip(graph, perms)])


def twin(nL, nR, K, graph):
    a = [random.randrange(K) for _ in range(nL)]
    b = [random.randrange(K) for _ in range(nR)]
    return game_on(nL, nR, K, graph,
                   [shift(K, b[v] - a[u]) for (u, v, w) in graph])


def check(cond, msg):
    if not cond:
        FAIL.append(msg)


def rand_perm(K):
    p = list(range(K))
    random.shuffle(p)
    return tuple(p)


def check_union_and_theorem_a(trials=25):
    worst = F(0)
    for t in range(trials):
        K = random.choice([2, 3])
        nL, nR = 2, 3
        graph = rand_graph(nL, nR, random.randint(4, 6))
        H = game_on(nL, nR, K, graph, [rand_perm(K) for _ in graph])
        S = twin(nL, nR, K, graph)
        sH = val(H)
        check(val(S) == 1, "twin not satisfiable")
        a, b = random.choice([(1, 1), (1, 2), (2, 1)])
        M = union(*([S] * a + [H] * b))
        N = union(*([H] * (a + b)))
        lam = F(a, a + b)
        c = val(M)
        check(c == lam + (1 - lam) * sH, "union value formula (item 1)")
        check(val(N) == sH, "copies of H keep the value")
        PS, PH, PM, PN = two_path(S), two_path(H), two_path(M), two_path(N)
        check(mass(PS) == mass(PH) == mass(S), "2-path mass is graph-only")
        vS, vH, vM, vN = val(PS), val(PH), val(PM), val(PN)
        check(vM == lam * vS + (1 - lam) * vH, "Phi(M) decomposes")
        check(vN == vH, "Phi(N) = Phi(H) in value")
        check(vM <= lam + (1 - lam) * vN, "Theorem A completeness step")
        if c < 1 and vM < 1:
            lhs = (1 - vN) / (1 - vM)
            rhs = (1 - sH) / (1 - c)
            check(lhs <= rhs, "Theorem A ratio bound")
            worst = max(worst, lhs / rhs)
    print("Theorem A: %d trials, max (R'/(1-s_H)/(1-c)) = %s = %.4f"
          % (trials, worst, float(worst)))


def check_products(trials=20):
    # val(G x G') <= min on random pieces with nL = 2, K = 2 (K^2 = 4, 4^4)
    for _ in range(trials):
        gs = []
        for _ in range(2):
            graph = rand_graph(2, 2, random.randint(3, 4))
            gs.append(game_on(2, 2, 2, graph, [rand_perm(2) for _ in graph]))
        v0, v1, v01 = val(gs[0]), val(gs[1]), val(tensor(gs[0], gs[1]))
        check(v01 <= min(v0, v1), "tensor value <= min")
        check(v01 >= v0 * v1, "tensor value >= product")
    # component decomposition of Y^(x2), Y = S + H0, one left vertex each.
    ident, swap = (0, 1), (1, 0)
    S = (1, 1, 2, [(0, 0, ident, F(2))])
    H0 = (1, 1, 2, [(0, 0, ident, F(1)), (0, 0, swap, F(1))])
    check(val(H0) == F(1, 2), "H0 value 1/2")
    Y = union(S, H0)
    Y2 = tensor(Y, Y)
    pieces = [tensor(A, B) for A in (S, H0) for B in (S, H0)]
    pred = sum(mass(P) * val(P) for P in pieces) / sum(mass(P) for P in pieces)
    check(val(Y2) == pred, "tensor square decomposes over component words")
    # Theorem B thresholds for t = 2..6 on the pair (c, s) with v0 = val H0.
    v0 = val(H0)
    for (c, s) in [(F(3, 4), F(5, 8)), (F(9, 10), F(3, 5)), (F(7, 10), F(11, 20))]:
        lY = (c - v0) / (1 - v0)
        lN = (s - v0) / (1 - v0)
        for t in range(2, 7):
            cp = lY ** t + (1 - lY ** t) * v0   # upper bound on c'
            sp = lN ** t                        # lower bound on s'
            Rp = (1 - sp) / (1 - cp)
            R = (1 - s) / (1 - c)
            check(Rp <= R / (1 - v0), "Theorem B bound")
    print("products: tensor<=min, decomposition and Theorem B bound checked")


def check_scalar(trials=2000):
    for _ in range(trials):
        x, y = sorted(F(random.randint(0, 999), 1000) for _ in range(2))
        if x == y:
            continue
        t = random.randint(1, 12)
        check((1 - x ** t) * (1 - y) <= (1 - x) * (1 - y ** t), "scalar")
    print("scalar inequality: %d trials" % trials)


def kms_numbers():
    for eps in [F(1, 10), F(1, 100), F(1, 1000)]:
        c, s = (1 - eps) / 2, eps
        R = (1 - s) / (1 - c)
        cap = 1 / (1 - c)
        check(cap < 2 and R < 2, "KMS cap below 2")
        print("eps=%s: R=%.5f, cap 1/(1-c)=%.5f < 2" % (eps, float(R), float(cap)))


if __name__ == "__main__":
    check_union_and_theorem_a()
    check_products()
    check_scalar()
    kms_numbers()
    if FAIL:
        print("FAILED:", sorted(set(FAIL)))
        sys.exit(1)
    print("ALL CHECKS PASSED")
