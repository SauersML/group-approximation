#!/usr/bin/env python3
"""Exact replay for research/artifacts/gap-floor-syndrome-separation-2026-09-16.md.

Checks (single-threaded, exact rational arithmetic unless stated):
  1. pair algebra: lambda_min(P+Q_N) = 2/d, <g,Pg> = <g,Q_N g> = 1/d, ker P cap ker Q_N = 0;
  2. feasibility factorization on small instances (triangle and 4-cycle plus pairs),
     by exact rank of the kernel intersections versus the predicted combinatorial rule;
  3. Petersen graph: girth 5, max degree 3, least monochromatic count 3 of 15 (>= 1/10),
     and every edge subset of size <= 4 is bipartite (the girth consequence used in Case A);
  4. the family's s*, lambda_min and least rounder constant on the Petersen member;
  5. the numeric inequalities used in the random-graph lemma.
This is supplementary replay; the artifact proves the universal statements.
"""
from fractions import Fraction as F
from itertools import combinations, product
import math


def pair(N):
    d = N * N + 1
    w = (F(2 * N, d), F(N * N - 1, d))
    P = [[F(0), F(0)], [F(0), F(1)]]
    Q = [[w[i] * w[j] for j in range(2)] for i in range(2)]
    return d, w, P, Q


def check_pair(N):
    d, w, P, Q = pair(N)
    assert w[0] ** 2 + w[1] ** 2 == 1
    K = [[P[i][j] + Q[i][j] for j in range(2)] for i in range(2)]
    tr = K[0][0] + K[1][1]
    det = K[0][0] * K[1][1] - K[0][1] * K[1][0]
    lam = F(2, d)
    # lam is a root of the characteristic polynomial and the smaller one (sum of roots = tr)
    assert lam * lam - tr * lam + det == 0 and tr - lam >= lam
    g = (N, -1)  # unnormalized; |g|^2 = d
    assert N * N + 1 == d
    Pg = sum(g[i] * P[i][j] * g[j] for i in range(2) for j in range(2)) / d
    Qg = sum(g[i] * Q[i][j] * g[j] for i in range(2) for j in range(2)) / d
    assert Pg == F(1, d) and Qg == F(1, d)
    # ker P = span(e0); Q e0 = w0 * w != 0
    assert Q[0][0] != 0 or Q[1][0] != 0
    return d


def kron(A, B):
    n, m = len(A), len(B)
    return [[A[i // m][j // m] * B[i % m][j % m] for j in range(n * m)] for i in range(n * m)]


def eye(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def embed(op, sites, nq):
    """op acts on the ordered qubit tuple `sites` (1 or 2 qubits) of nq qubits."""
    k = len(sites)
    dim = 2 ** nq
    M = [[F(0)] * dim for _ in range(dim)]
    for col in range(dim):
        bits = [(col >> (nq - 1 - q)) & 1 for q in range(nq)]
        sub = 0
        for s in sites:
            sub = 2 * sub + bits[s]
        for r in range(2 ** k):
            val = op[r][sub]
            if val == 0:
                continue
            nb = list(bits)
            for idx, s in enumerate(sites):
                nb[s] = (r >> (k - 1 - idx)) & 1
            row = 0
            for b in nb:
                row = 2 * row + b
            M[row][col] += val
    return M


def rank(rows):
    A = [list(r) for r in rows]
    rk, ncols = 0, len(A[0]) if A else 0
    for c in range(ncols):
        piv = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        inv = 1 / A[rk][c]
        A[rk] = [x * inv for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def satisfiable(edges, nv):
    for x in product((0, 1), repeat=nv):
        if all(x[u] != x[v] for u, v in edges):
            return True
    return False


def check_factorization(edges, nv, npairs, N):
    d, w, P, Q = pair(N)
    ne = [[F(0)] * 4 for _ in range(4)]
    ne[0][0] = F(1)
    ne[3][3] = F(1)
    nq = nv + npairs
    terms, labels = [], []
    for (u, v) in edges:
        terms.append(embed(ne, (u, v), nq))
        labels.append(("e", (u, v)))
    for j in range(npairs):
        terms.append(embed(P, (nv + j,), nq))
        labels.append(("P", j))
        terms.append(embed(Q, (nv + j,), nq))
        labels.append(("Q", j))
    m, dim = len(terms), 2 ** nq
    count = 0
    for mask in range(2 ** m):
        S = {i for i in range(m) if mask >> i & 1}
        outside = [i for i in range(m) if i not in S]
        # kernel of a sum of positive matrices is the intersection of their kernels
        total = [[sum(terms[i][r][c] for i in outside) for c in range(dim)] for r in range(dim)]
        feasible_numeric = (not outside) or rank(total) < dim
        out_edges = [labels[i][1] for i in range(m) if labels[i][0] == "e" and i not in S]
        pairs_hit = all(any(i in S for i in range(m) if labels[i][1] == j and labels[i][0] in "PQ")
                        for j in range(npairs))
        feasible_rule = satisfiable(out_edges, nv) and pairs_hit
        assert feasible_numeric == feasible_rule, (edges, S)
        count += 1
    return count


def petersen():
    outer = [(i, (i + 1) % 5) for i in range(5)]
    spokes = [(i, i + 5) for i in range(5)]
    inner = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    return outer + spokes + inner


def girth(edges, nv):
    adj = {v: set() for v in range(nv)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    best = math.inf
    for s in range(nv):
        dist, par, queue = {s: 0}, {s: -1}, [s]
        for u in queue:
            for v in adj[u]:
                if v not in dist:
                    dist[v], par[v] = dist[u] + 1, u
                    queue.append(v)
                elif par[u] != v:
                    best = min(best, dist[u] + dist[v] + 1)
    return best


def main():
    for N in range(2, 60):
        check_pair(N)
    print("pair algebra: OK for N=2..59")

    tri = [(0, 1), (1, 2), (0, 2)]
    sq = [(0, 1), (1, 2), (2, 3), (0, 3)]
    n1 = check_factorization(tri, 3, 2, 2)
    n2 = check_factorization(sq, 4, 1, 3)
    print(f"feasibility factorization: OK ({n1} subsets on triangle+2 pairs, {n2} on 4-cycle+1 pair)")

    E = petersen()
    nv = 10
    deg = [sum(v in e for e in E) for v in range(nv)]
    g5 = girth(E, nv)
    mono = min(sum(x[u] == x[v] for u, v in E) for x in product((0, 1), repeat=nv))
    assert len(E) == 15 and max(deg) == 3 and g5 == 5 and mono == 3 and 10 * mono >= len(E)
    small = sum(1 for k in range(1, 5) for sub in combinations(E, k))
    assert all(satisfiable(list(sub), nv) for k in range(1, 5) for sub in combinations(E, k))
    print(f"Petersen: girth {g5}, max degree {max(deg)}, least monochromatic {mono}/15; "
          f"all {small} edge sets of size <= 4 bipartite: OK")

    mc = len(E)
    m = 3 * mc
    for N in (2, 5, 20):
        d = N * N + 1
        s_star = mono + mc
        lam = F(mono, m) + F(2 * mc, d * m)
        cmin = F(s_star, m) / lam
        assert F(s_star, m) >= F(11, 30) and lam >= F(1, 30) and cmin <= 11
        print(f"Petersen member N={N}: s*/m={F(s_star, m)}, lambda_min={lam}, C_min={cmin}")

    D, Delta = 64, 512
    assert (1 - math.log(2)) / 2 > 1 / 8
    assert F(D, 6 * (D - 1)) <= 1
    lg_a = (4 + 100 * (math.log(2) - 2)) / math.log(10)
    lg_d = (math.log(800 / 7) + Delta * (1 - math.log(8))) / math.log(10)
    assert lg_a < -50 and lg_d < -200
    assert math.lgamma(Delta + 1) >= Delta * (math.log(Delta) - 1)
    assert F(D, Delta + 1) <= F(1, 8)
    assert F(672 * 100 - 1600, 6400 * 100) >= F(1, 10)
    fail = 0.25 + 2 / (D * 100) + 10 ** lg_a + 10 ** lg_d
    assert fail < 1
    print(f"random-graph constants: log10 bounds {lg_a:.1f}, {lg_d:.1f}; failure prob < {fail:.6f}: OK")


if __name__ == "__main__":
    main()
