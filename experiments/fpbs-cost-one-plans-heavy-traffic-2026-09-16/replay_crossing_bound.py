#!/usr/bin/env python3
"""Finite replay of the counting core of the heavy-traffic crossing bound.

Scope: a finite group Gamma acting on itself by right multiplication, with
uniform measure.  A random finite routing plan (edge copies phi_j = R_{g_j}|A_j,
shortest-path routes of bounded length for the generator requests) is built,
uncovered requests are augmented by direct copies, markers are chosen as a
maximal 2R-separated set, Voronoi cells with (distance, marker order)
tie-breaking and parent trees are formed, and the following are checked
exactly (fractions):

  (i)   change of variables: sum_j sum_z k_j(z) = total route length;
  (ii)  augmentation keeps B and every Tail_T, and gives full coverage;
  (iii) cells are connected, parent edges form spanning trees, and
        B_H(m,R) is contained in the cell of m when |component| > R;
  (iv)  crossing copies have measure <= sum_j nu(U_j) - nu(Y minus markers);
  (v)   pointwise k <= T+1+Q 1_{Q>T} on used copies;
  (vi)  boundary(K) <= sum over crossing copies of k
                    <= (T+1) nu(cross) + Tail_T
                    <= (T+1)(B-1+nu(markers)) + Tail_T.

For a finite group the Cheeger constant of Gamma itself is zero, so this is a
replay of the finite counting inequalities only, not of the infinite
mass-transport lower bound boundary(K) >= h_S.  Single-threaded, small.
"""
import itertools
import json
import random
import sys
from collections import deque
from fractions import Fraction

TS = [Fraction(0), Fraction(1, 2), Fraction(1), Fraction(2), Fraction(3), Fraction(5)]


def perm_group(gens, n):
    """Return (elements, mult table index, generator indices) for a permutation group."""
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        new = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[i]] for i in range(n))
                if q not in index:
                    index[q] = len(elems)
                    elems.append(q)
                    new.append(q)
        frontier = new
    N = len(elems)
    mult = [[0] * N for _ in range(N)]
    for a in range(N):
        pa = elems[a]
        for b in range(N):
            pb = elems[b]
            mult[a][b] = index[tuple(pb[pa[i]] for i in range(n))]
    gidx = [index[tuple(g)] for g in gens]
    return N, mult, gidx


def abelian_group(ns, gens):
    elems = list(itertools.product(*[range(k) for k in ns]))
    index = {e: i for i, e in enumerate(elems)}
    N = len(elems)
    mult = [[index[tuple((a[i] + b[i]) % ns[i] for i in range(len(ns)))] for b in elems] for a in elems]
    gidx = [index[tuple(g)] for g in gens]
    return N, mult, gidx


def inverse_table(N, mult):
    inv = [0] * N
    for a in range(N):
        for b in range(N):
            if mult[a][b] == 0:
                inv[a] = b
    return inv


def run_trial(rng, N, mult, S, m, p, L, R):
    inv = inverse_table(N, mult)
    copies = []  # (label g, domain set)
    for _ in range(m):
        g = rng.randrange(1, N)
        A = frozenset(z for z in range(N) if rng.random() < p)
        copies.append((g, A))
    # adjacency: from vertex x, hop via copy j forward (x in A_j -> x g_j) or
    # backward (x g_j^{-1} in A_j -> x g_j^{-1}); the copy is identified by its
    # forward start.
    def hops(x, cps):
        out = []
        for j, (g, A) in enumerate(cps):
            if x in A:
                out.append((mult[x][g], (j, x)))
            w = mult[x][inv[g]]
            if w in A:
                out.append((w, (j, w)))
        return out

    routes = {}
    for s in S:
        for y in range(N):
            target = mult[y][s]
            prev = {y: None}
            dq = deque([(y, 0)])
            found = False
            while dq:
                x, d = dq.popleft()
                if x == target:
                    found = True
                    break
                if d == L:
                    continue
                for w, cid in hops(x, copies):
                    if w not in prev:
                        prev[w] = (x, cid)
                        dq.append((w, d + 1))
            if found:
                path = []
                x = target
                while prev[x] is not None:
                    px, cid = prev[x]
                    path.append(cid)
                    x = px
                routes[(s, y)] = list(reversed(path))
    k = {}
    for path in routes.values():
        for cid in path:
            k[cid] = k.get(cid, 0) + 1
    total_len = sum(len(pth) for pth in routes.values())
    assert sum(k.values()) == total_len, "change of variables"  # (i)
    uncovered = [(s, y) for s in S for y in range(N) if (s, y) not in routes]
    B = Fraction(len(k) + len(uncovered), N)

    def tail(kd, T):
        return Fraction(sum((v - 1) for v in kd.values() if (v - 1) > T), N)

    tails_before = [tail(k, T) for T in TS]
    # augmentation: new copy per uncovered request with label s, domain {y}
    aug = [(g, frozenset(z for z in A if (j, z) in k)) for j, (g, A) in enumerate(copies)]
    k2 = dict(k)
    routes2 = dict(routes)
    base = len(aug)
    for i, (s, y) in enumerate(uncovered):
        aug.append((s, frozenset([y])))
        k2[(base + i, y)] = 1
        routes2[(s, y)] = [(base + i, y)]
    B2 = Fraction(len(k2), N)
    assert B2 == B and all(routes2.get((s, y)) is not None for s in S for y in range(N))  # (ii)
    assert [tail(k2, T) for T in TS] == tails_before  # (ii)
    used = set(k2.keys())
    # H-distances within 2R, markers
    def ball(x, rad):
        dist = {x: 0}
        dq = deque([x])
        while dq:
            u = dq.popleft()
            if dist[u] == rad:
                continue
            for w, cid in hops(u, aug):
                if cid in used and w not in dist:
                    dist[w] = dist[u] + 1
                    dq.append(w)
        return dist
    order = list(range(N))
    rng.shuffle(order)
    rank = {x: i for i, x in enumerate(order)}
    markers = []
    for x in order:
        bx = ball(x, 2 * R)
        if all(mk not in bx for mk in markers):
            markers.append(x)
    mball = {mk: ball(mk, 2 * R) for mk in markers}
    cell = {}
    for x in range(N):
        cands = [(mball[mk][x], rank[mk], mk) for mk in markers if x in mball[mk]]
        assert cands, "maximality"
        cell[x] = min(cands)[2]
    comp_size = len(ball(0, N))
    ncross = 0
    parent_copies = set()
    for x in range(N):
        mk = cell[x]
        d = mball[mk][x]
        if d == 0:
            continue
        opts = [(w, cid) for w, cid in hops(x, aug) if cid in used and mball[mk].get(w, -1) == d - 1]
        assert opts
        w, cid = opts[0]
        assert cell[w] == mk, "geodesic parent stays in cell"  # (iii)
        assert cid not in parent_copies
        parent_copies.add(cid)
    assert len(parent_copies) == N - len(markers)  # tree edge count
    for mk in markers:
        cellset = {x for x in range(N) if cell[x] == mk}
        if comp_size > R:
            assert set(x for x, d in mball[mk].items() if d <= R) <= cellset  # (iii)
    cross = [cid for cid in used if cell[cid[1]] != cell[mult[cid[1]][aug[cid[0]][0]]]]
    ncross = len(cross)
    assert not (set(cross) & parent_copies)
    nu_cross = Fraction(ncross, N)
    assert nu_cross <= B2 - Fraction(N - len(markers), N)  # (iv)
    boundary = Fraction(sum(1 for s in S for y in range(N) if cell[mult[y][s]] != cell[y]), N)
    cross_traffic = Fraction(sum(k2[c] for c in cross), N)
    assert boundary <= cross_traffic
    worst_slack = None
    for T in TS:
        for v in k2.values():
            q = v - 1
            assert v <= T + 1 + (q if q > T else 0)  # (v)
        t = tail(k2, T)
        rhs1 = (T + 1) * nu_cross + t
        rhs2 = (T + 1) * (B2 - 1 + Fraction(len(markers), N)) + t
        assert cross_traffic <= rhs1 <= rhs2  # (vi)
        slack = rhs2 - boundary
        worst_slack = slack if worst_slack is None else min(worst_slack, slack)
    return {"B": str(B), "markers": len(markers), "boundary": str(boundary),
            "uncovered": len(uncovered), "min_slack": str(worst_slack)}


def main():
    rng = random.Random(20260916)
    groups = []
    groups.append(("Z_40", abelian_group([40], [(1,)])))
    groups.append(("Z_12xZ_6", abelian_group([12, 6], [(1, 0), (0, 1)])))
    s4 = [(1, 0, 2, 3), (1, 2, 3, 0)]
    groups.append(("S_4", perm_group(s4, 4)))
    a5 = [(1, 2, 0, 3, 4), (0, 1, 3, 4, 2), (1, 0, 3, 2, 4)]
    groups.append(("A_5_three_gens", perm_group(a5, 5)))
    records = {}
    trials = 0
    for name, (N, mult, S) in groups:
        rec = []
        for t in range(40):
            m = rng.randint(1, 5)
            p = rng.choice([0.2, 0.4, 0.6, 0.9])
            L = rng.randint(1, 6)
            R = rng.randint(1, 4)
            rec.append(run_trial(rng, N, mult, S, m, p, L, R))
            trials += 1
        records[name] = {"order": N, "trials": len(rec),
                         "min_slack": str(min(Fraction(r["min_slack"]) for r in rec)),
                         "max_uncovered": max(r["uncovered"] for r in rec)}
    out = {"status": "passed", "trials": trials, "cutoffs": [str(T) for T in TS], "groups": records}
    json.dump(out, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
