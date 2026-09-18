#!/usr/bin/env python3
"""Steenbock's explicit generalized Rips--Segev graphs (arXiv:1307.0981, Sec. "Explicit constructions").

Phi is a covering of the bouquet of four circles x_1..x_4: permutations sigma_1..sigma_4 of the lines
{0..n-1}; an x_j-edge l -> i means sigma_j(l) = i.  Line i uses row r(i) of the table
(I1, I2, O1, O2, C) = (10^{5r-4}, ..., 10^{5r}).  Steenbock's relabelling gives the b-edges
  x_{i1} = b a^{-I_i1}          : v_{l,0}      -> v_{i,I_i1}   (l = sigma_1^{-1}(i))
  x_{i2} = a^{C_l} b a^{-I_i2}  : v_{l,C_l}    -> v_{i,I_i2}   (l = sigma_2^{-1}(i))
  y_{i3} = a^{O_i1} b a^{-C_k}  : v_{i,O_i1}   -> v_{k,C_k}    (k = sigma_3(i))
  y_{i4} = a^{O_i2} b           : v_{i,O_i2}   -> v_{k,0}      (k = sigma_4(i))
Gamma is represented implicitly by its distinguished vertices (i, position).

Checks (claim rips-segev-steenbock-few-line-a-supports-are-regular):
 (S1) every vertex of Gamma has at most one outgoing and at most one incoming b-edge;
 (S2) maximal runs of b-edges of one orientation have at most 2 edges;
 (S3) a b-edge joins two vertices of one line iff the corresponding Phi-edge is a loop;
 (S4) the distances between distinguished positions are nonzero and pairwise distinct over all lines
      (Rips--Segev condition) and at least 10; the least one on row r is 10^{5r-4};
 (S5) exhaustive search of backtrack-free chains b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q} with every
      |n_k| <= M: whenever the projected Phi-walk (one Phi-edge per b-edge) has length < girth(Phi), the
      hop lines are pairwise distinct and lie in L_S, so q <= |L_S|.
 Control: with a loop of Phi at the row-1 line (sigma_1 fixing it), the b-edge v_{1,0} -> v_{1,10} appears
 and a chain with two hops on line 1 exists, so the girth hypothesis is used.
Usage: python3 steenbock_chains.py [seed ...]
"""
import random
import sys
from collections import deque


def table(r):
    return tuple(10 ** (5 * r - 4 + t) for t in range(5))  # I1, I2, O1, O2, C


def build(n, seed, loop_row1=False, girth_target=0, cluster=False):
    rng = random.Random(seed)
    sig = [list(range(n)) for _ in range(4)]
    for s in sig:
        rng.shuffle(s)
    rows = list(range(1, n + 1))
    rng.shuffle(rows)
    if girth_target:
        improve_girth(n, sig, girth_target, rng)
    if cluster:
        # rows 1, 2, 3, ... on a BFS ball of Phi around line 0, so the lines of small L_S are adjacent
        adj = adjacency(n, sig)
        order, seen, dq = [], {0}, deque([0])
        while dq:
            u = dq.popleft()
            order.append(u)
            for (w, e) in adj[u]:
                if w not in seen:
                    seen.add(w)
                    dq.append(w)
        order += [v for v in range(n) if v not in seen]
        for r, v in enumerate(order):
            rows[v] = r + 1
    if loop_row1:
        i1 = rows.index(1)
        j = sig[0].index(i1)  # make sigma_1(i1) = i1 by a swap
        sig[0][i1], sig[0][j] = sig[0][j], sig[0][i1]
    coef = [table(r) for r in rows]
    edges = []  # (source vertex, target vertex, phi-edge id)
    for l in range(n):
        i = sig[0][l]
        edges.append(((l, 0), (i, coef[i][0]), (0, l)))
        i = sig[1][l]
        edges.append(((l, coef[l][4]), (i, coef[i][1]), (1, l)))
        k = sig[2][l]
        edges.append(((l, coef[l][2]), (k, coef[k][4]), (2, l)))
        k = sig[3][l]
        edges.append(((l, coef[l][3]), (k, 0), (3, l)))
    return rows, coef, sig, edges


def adjacency(n, sig):
    adj = [[] for _ in range(n)]
    for j in range(4):
        for l in range(n):
            e = (j, l)
            adj[l].append((sig[j][l], e))
            adj[sig[j][l]].append((l, e))
    return adj


def cycle_edge_near(adj, s, depth):
    dist = {s: 0}
    par = {s: None}
    dq = deque([s])
    while dq:
        u = dq.popleft()
        if dist[u] >= depth:
            continue
        for (w, e) in adj[u]:
            if e == par[u]:
                continue
            if w in dist:
                return e
            dist[w] = dist[u] + 1
            par[w] = e
            dq.append(w)
    return None


def improve_girth(n, sig, target, rng, rounds=200000):
    """Random swaps sigma_j(l) <-> sigma_j(m) until no cycle of length < target is seen from any vertex."""
    depth = target // 2
    for _ in range(rounds):
        adj = adjacency(n, sig)
        bad = None
        for s in rng.sample(range(n), n):
            e = cycle_edge_near(adj, s, depth)
            if e is not None:
                bad = e
                break
        if bad is None:
            return
        j, l = bad
        m = rng.randrange(n)
        sig[j][l], sig[j][m] = sig[j][m], sig[j][l]
    raise RuntimeError("girth target not reached")


def girth(n, sig):
    adj = [[] for _ in range(n)]
    for j in range(4):
        for l in range(n):
            e = (j, l)
            adj[l].append((sig[j][l], e))
            adj[sig[j][l]].append((l, e))
    best = 10 ** 9
    for s in range(n):
        for (t, e) in adj[s]:
            if t == s:
                return 1
        dist = {s: 0}
        par = {s: None}
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for (w, e) in adj[u]:
                if e == par[u]:
                    continue
                if w in dist:
                    best = min(best, dist[u] + dist[w] + 1)
                else:
                    dist[w] = dist[u] + 1
                    par[w] = e
                    dq.append(w)
    return best


def check_structure(n, rows, coef, edges):
    out, inn = {}, {}
    for (s, t, e) in edges:
        assert s not in out, ("two outgoing b-edges", s)
        assert t not in inn, ("two incoming b-edges", t)
        out[s], inn[t] = (t, e), (s, e)
    # (S2): a run of two forward edges s -> u -> w has u in out and in inn; then w must not be a source
    maxrun = 1
    for (s, t, e) in edges:
        if t in out:
            w = out[t][0]
            maxrun = max(maxrun, 2)
            assert w not in out, "b-run of length 3"
    # (S3)
    same_line = sum(1 for (s, t, e) in edges if s[0] == t[0])
    # (S4)
    dists = {}
    for i in range(n):
        D = sorted({0} | set(coef[i]))
        for x in range(len(D)):
            for y in range(x + 1, len(D)):
                d = D[y] - D[x]
                assert d not in dists, "Rips-Segev condition fails"
                dists[d] = i
        assert min(D[1:]) == 10 ** (5 * rows[i] - 4)
    assert min(dists) >= 10
    return out, inn, maxrun, same_line


def chains(n, coef, out, inn, M, qmax, starts):
    """Enumerate hop sequences.  A state is (vertex, last b-edge used); a chain alternates a hop
    (0 < |p'-p| <= M between distinguished positions of one line) and a b-run of 1 or 2 edges of one
    orientation.  Yields (hop lines, Phi-walk length)."""
    D = [sorted({0} | set(c)) for c in coef]
    res = []

    def runs(v):
        # all b-runs starting at v: forward (v a source) or backward (v a target), length 1 or 2
        r = []
        if v in out:
            u, e = out[v]
            r.append((u, 1))
            if u in out:
                r.append((out[u][0], 2))
        if v in inn:
            u, e = inn[v]
            r.append((u, 1))
            if u in inn:
                r.append((inn[u][0], 2))
        return r

    def dfs(v, lines, walk, inner):
        # inner = Phi-walk length from the first hop line to the last hop line
        if lines:
            res.append((tuple(lines), inner))
        if len(lines) >= qmax:
            return
        i, p = v
        for p2 in D[i]:
            if p2 != p and abs(p2 - p) <= M:
                for (u, ln) in runs((i, p2)):
                    dfs(u, lines + [i], walk + ln, walk)

    for i in starts:
        for p in D[i]:
            if (i, p) in out or (i, p) in inn:
                dfs((i, p), [], 0, 0)
    return res


def main():
    seeds = [int(x) for x in sys.argv[1:]] or [1, 2, 3]
    n = 1500
    for seed in seeds:
        for (gt, loop, cl) in ((5, False, False), (5, True, False), (5, False, True), (0, False, True)):
            rows, coef, sig, edges = build(n, seed, loop_row1=loop, girth_target=gt, cluster=cl)
            g = girth(n, sig)
            out, inn, maxrun, same = check_structure(n, rows, coef, edges)
            loops = sum(1 for j in range(4) for l in range(n) if sig[j][l] == l)
            assert same == loops, "(S3) fails"
            row1 = rows.index(1)
            has_edge = ((row1, 0) in out and out[(row1, 0)][0] == (row1, 10))
            print(f"seed={seed} loop_row1={loop} clustered_rows={cl} n={n} girth(Phi)={g} max_b_run={maxrun} "
                  f"same_line_b_edges={same}=loops(Phi) b_edge_v1,0->v1,10={has_edge}")
            for M in (89, 10 ** 6, 10 ** 11, 10 ** 16, 10 ** 26, 10 ** 36):
                LS = {i for i in range(n) if 10 ** (5 * rows[i] - 4) <= M}
                ch = chains(n, coef, out, inn, M, 6, sorted(LS))
                short = [c for c in ch if c[1] < g]
                bad = [c for c in short if len(set(c[0])) < len(c[0]) or not set(c[0]) <= LS]
                rep = [c for c in ch if len(set(c[0])) < len(c[0])]
                print(f"   M={M} |L_S|={len(LS)} chains={len(ch)} (walk<girth: {len(short)}, "
                      f"violations {len(bad)}, longest {max((len(c[0]) for c in short), default=0)}) "
                      f"longest_any={max((len(c[0]) for c in ch), default=0)} "
                      f"repeating_a_line={len(rep)} min_walk_of_repeating={min((c[1] for c in rep), default=None)}")
                assert not bad


if __name__ == "__main__":
    main()
