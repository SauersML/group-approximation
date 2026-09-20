#!/usr/bin/env python3
"""Exhaustive check of the digraph part of one-sink-class-below-twice-the-minimum-proof.

Model. A digraph R on m letters, every letter with an out-arc (every pattern has an output).
Axioms proved in Step 1 / Step 2 of the route, for a strict automaton with n0 = min NS(G):
  (A1) every nonempty proper forward-closed set has size in N (a set of allowed sizes, min N = n0);
  (A2) for every sink class C of period d >= 2, each cyclic class has size in N
       (it is a proper upset of the d-th power).
The script enumerates every digraph with m <= 4 vertices and samples random digraphs with m = 5, 6.
For each admissible R it checks:
  item 1: #sink classes r = 1, or r * n0 <= m; each sink class C of period d has d * n0 <= |C|;
  item 2: m < 2 n0  =>  exactly one sink class, which is primitive and inside every nonempty upset;
  item 3: m < 2 n0 and N ∩ (n0, m) empty  =>  strongly connected, or exactly two classes of sizes n0, m - n0;
  item 4: m = n0 + 1  =>  strongly connected, or the non-sink part is one letter whose complement is an upset.
It also reports how many admissible digraphs are not strongly connected in each case, to show the
second alternatives actually occur at the digraph level.
"""
import itertools
import math
import random


def sccs(m, adj):
    index, low, onst, st, comps, cnt = {}, {}, set(), [], [], [0]

    def dfs(v):
        index[v] = low[v] = cnt[0]
        cnt[0] += 1
        st.append(v)
        onst.add(v)
        for w in adj[v]:
            if w not in index:
                dfs(w)
                low[v] = min(low[v], low[w])
            elif w in onst:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = set()
            while True:
                w = st.pop()
                onst.discard(w)
                comp.add(w)
                if w == v:
                    break
            comps.append(frozenset(comp))

    for v in range(m):
        if v not in index:
            dfs(v)
    return comps


def closure(adj, start):
    seen, stack = set(start), list(start)
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return frozenset(seen)


def period_and_classes(comp, adj):
    root = min(comp)
    level, order = {root: 0}, [root]
    for v in order:
        for w in adj[v]:
            if w in comp and w not in level:
                level[w] = level[v] + 1
                order.append(w)
    d = 0
    for v in comp:
        for w in adj[v]:
            if w in comp:
                d = math.gcd(d, level[v] + 1 - level[w])
    d = abs(d)
    if d == 0:  # single vertex without loop cannot occur in a sink class (out-arc needed)
        return 0, []
    cls = {}
    for v in comp:
        cls.setdefault(level[v] % d, set()).add(v)
    return d, [frozenset(c) for c in cls.values()]


def analyse(m, adj, n0, N):
    full = frozenset(range(m))
    upsets = set()
    for r in range(1, m):
        for S in itertools.combinations(range(m), r):
            S = frozenset(S)
            if all(w in S for v in S for w in adj[v]):
                upsets.add(S)
    if any(len(U) not in N for U in upsets):
        return None
    comps = sccs(m, adj)
    sinks = [C for C in comps if all(w in C for v in C for w in adj[v])]
    info = []
    for C in sinks:
        d, cyc = period_and_classes(C, adj)
        if d >= 2 and any(len(V) not in N for V in cyc):
            return None
        info.append((C, d))
    return comps, sinks, info, upsets, full


def check(m, adj, n0, N, stats):
    res = analyse(m, adj, n0, N)
    if res is None:
        return
    comps, sinks, info, upsets, full = res
    key = (m, n0, tuple(sorted(N)))
    s = stats.setdefault(key, [0, 0])
    s[0] += 1
    sc = len(comps) == 1
    if not sc:
        s[1] += 1
    r = len(sinks)
    assert r == 1 or r * n0 <= m, (m, adj)
    for C, d in info:
        assert d * n0 <= len(C) or (d == 1 and len(C) >= n0), (m, adj, C, d)
    if m < 2 * n0:
        assert r == 1, (m, adj)
        C, d = info[0]
        assert d == 1, (m, adj)
        assert all(C <= U for U in upsets), (m, adj)
        if not any(n0 < x < m for x in N):
            assert sc or (len(comps) == 2 and sorted(map(len, comps)) == sorted([n0, m - n0])), (m, adj)
    if m == n0 + 1 and not sc:
        C = sinks[0]
        T = full - C
        assert len(T) == 1 and C in upsets, (m, adj)


def digraphs(m, exhaustive, samples, rng):
    pairs = [(a, b) for a in range(m) for b in range(m)]
    if exhaustive:
        for mask in range(1 << len(pairs)):
            yield [[b for (a, b), i in zip(pairs, range(len(pairs))) if a == v and mask >> i & 1] for v in range(m)]
    else:
        for _ in range(samples):
            p = rng.choice([0.2, 0.35, 0.5])
            yield [[b for b in range(m) if rng.random() < p] for v in range(m)]


def main():
    rng = random.Random(20260917)
    stats = {}
    for m in range(2, 7):
        exhaustive = m <= 4
        for adj in digraphs(m, exhaustive, 60000, rng):
            if any(not out for out in adj):
                continue
            for n0 in range(2, m + 1):
                # allowed sizes: n0 plus any subset of (n0, m); m itself is the automaton's own size
                mids = list(range(n0 + 1, m))
                for r in range(len(mids) + 1):
                    for extra in itertools.combinations(mids, r):
                        N = {n0, *extra}
                        check(m, adj, n0, N, stats)
    for key in sorted(stats):
        tot, nsc = stats[key]
        print(f"m={key[0]} n0={key[1]} N={list(key[2])}: admissible={tot} not-strongly-connected={nsc}")
    print("all assertions passed")


if __name__ == "__main__":
    main()
