"""Integral anti-flag graphs and RACG subgraphs with positive Euler characteristic.

A vertex is an anti-flag (p, L): primitive p, L in Z^3 (up to sign) with L.p in {1, 2}
(after sign choice).  Its reflection s = I - (2/(L.p)) p L^T lies in GL_3(Z).
Two anti-flags commute iff L.p' = L'.p = 0 (mutual incidence) -- an edge.
Every induced subgraph Gamma of this graph is realized in GL_3(Z) by reflections, with
non-edges of infinite order unless (L.p')(L'.p)*4/((L.p)(L'.p')) in {1,2,3}.

We search induced subgraphs that are triangle-free, K_{2,3}-free (no Z x F_2), all non-edges of
infinite order, with chi = 1 - V/2 + E/4 > 0.
"""
import itertools, random, sys
import numpy as np


def prim_vectors(B):
    out = []
    for v in itertools.product(range(-B, B + 1), repeat=3):
        if v == (0, 0, 0):
            continue
        if np.gcd.reduce([abs(c) for c in v]) != 1:
            continue
        # canonical sign: first nonzero positive
        nz = next(c for c in v if c != 0)
        if nz > 0:
            out.append(v)
    return out


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def build(B):
    P = prim_vectors(B)
    verts = []
    for p in P:
        for L in P:
            d = dot(p, L)
            if abs(d) in (1, 2):
                Ls = L if d > 0 else tuple(-c for c in L)
                verts.append((p, Ls, abs(d)))
    return verts


def cartan(x, y):
    # a_xy = beta_x . alpha_y with alpha = p, beta = 2 L /(L.p)
    return 2 * dot(x[1], y[0]) / x[2]


def edge(x, y):
    return dot(x[1], y[0]) == 0 and dot(y[1], x[0]) == 0


def finite_order_nonedge(x, y):
    if edge(x, y):
        return False
    pr = cartan(x, y) * cartan(y, x)
    return abs(pr - round(pr)) < 1e-9 and round(pr) in (1, 2, 3)


def reflection(x):
    p, L, d = x
    return np.eye(3, dtype=np.int64) - (2 // d) * np.outer(p, L) if d in (1, 2) else None


def graph(verts):
    n = len(verts)
    A = [set() for _ in range(n)]
    bad = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if edge(verts[i], verts[j]):
                A[i].add(j); A[j].add(i)
            elif finite_order_nonedge(verts[i], verts[j]):
                bad[i].add(j); bad[j].add(i)
    return A, bad


def ok_add(S, v, A, bad):
    """Can v be added to induced subgraph S keeping triangle-free, K23-free, no finite non-edges?"""
    if bad[v] & S:
        return False
    Nv = A[v] & S
    # triangle: two neighbours of v adjacent
    for u in Nv:
        if A[u] & Nv:
            return False
    # K_{2,3}: v and some w in S share >= 3 common neighbours in S, or v is one of the 3
    for w in S:
        if w in A[v]:
            continue
        if len(A[w] & Nv) >= 3:
            return False
    # v as a middle vertex: pairs of its neighbours (nonadjacent) sharing >=2 other common nbrs
    for u, w in itertools.combinations(Nv, 2):
        if len(A[u] & A[w] & S) >= 2:
            return False
    return True


def search(A, bad, iters=200000, seed=0, T0=2.0):
    import math
    rng = random.Random(seed); n = len(A)
    S = set(); E = 0
    best = (-10 ** 9, None)
    for it in range(iters):
        T = T0 * (1 - it / iters) + 0.05
        v = rng.randrange(n)
        if v in S:
            dE = len(A[v] & S); d = 2 - dE
            if d >= 0 or rng.random() < math.exp(d / T):
                S.remove(v); E -= dE
        elif AF_ok(S, v, A, bad):
            dE = len(A[v] & S); d = dE - 2
            if d >= 0 or rng.random() < math.exp(d / T):
                S.add(v); E += dE
        score = 4 - 2 * len(S) + E  # = 4 chi
        if len(S) > 2 and score > best[0]:
            best = (score, set(S))
    return best


def AF_ok(S, v, A, bad):
    import antiflag
    return antiflag.ok_add(S, v, A, bad)


if __name__ == '__main__':
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    iters = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    verts = build(B)
    A, bad = graph(verts)
    print("B", B, "antiflags", len(verts), "max degree", max(len(a) for a in A))
    for seed in range(int(sys.argv[3]) if len(sys.argv) > 3 else 4):
        sc, S = search(A, bad, iters, seed)
        S = sorted(S); E = sum(len(A[v] & set(S)) for v in S) // 2
        print(f"seed {seed}: 4chi={sc} V={len(S)} E={E}")
        if sc > 0:
            print("  POSITIVE", [verts[v] for v in S])
