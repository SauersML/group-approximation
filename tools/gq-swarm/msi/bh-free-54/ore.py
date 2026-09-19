#!/usr/bin/env python3
"""Ore condition and spine growth for the edge-stellar operad O_E on the cone Delta in R^3.

O_E-dissections of a unimodular triangle T are obtained from {T} by repeatedly splitting a
piece (p,q,r) at an edge midpoint u = p+q into (p,u,r),(u,q,r).  D >=_E D' means D is obtained
from D' by such splits (D = D' o psi with psi in O_E).

modes:
  ore N            for all pairs of O_E-dissections of Delta with 2..4 pieces, the smallest
                   common O_E-upper bound with <= N pieces (or none)
  spine N ROUNDS   Thumann spine iteration from the three atoms, inside sizes <= N
  access N         is T=cone((0,1,3),(1,1,1),(2,1,0)) a union of pieces of some O_E-dissection
                   with <= N pieces whose restriction to T is O_E relative to T?
"""
import sys, json, time
from collections import defaultdict

E0, E1, E2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)


def det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def tri(a, b, c):
    return tuple(sorted((a, b, c)))


DELTA = tri(E0, E1, E2)


def splits(t):
    a, b, c = t
    out = []
    for (p, q, r) in ((a, b, c), (a, c, b), (b, c, a)):
        u = add(p, q)
        out.append((tri(p, u, r), tri(u, q, r)))
    return out


def up(D, N):
    """All O_E-refinements of D with at most N pieces."""
    seen = {D}
    frontier = [D]
    while frontier:
        new = []
        for X in frontier:
            if len(X) >= N:
                continue
            for t in X:
                for P1, P2 in splits(t):
                    G = frozenset((X - {t}) | {P1, P2})
                    if G not in seen:
                        seen.add(G)
                        new.append(G)
        frontier = new
    return seen


def inside(x, T):
    a, b, c = T
    D = det(a, b, c)
    return det(x, b, c) * D >= 0 and det(a, x, c) * D >= 0 and det(a, b, x) * D >= 0


memo = {}


def hier(T, pieces):
    if len(pieces) == 1:
        return next(iter(pieces)) == T
    key = (T, pieces)
    if key in memo:
        return memo[key]
    res = False
    for P1, P2 in splits(T):
        s1 = frozenset(p for p in pieces if all(inside(x, P1) for x in p))
        s2 = frozenset(p for p in pieces if all(inside(x, P2) for x in p))
        if s1 and s2 and len(s1) + len(s2) == len(pieces) and hier(P1, s1) and hier(P2, s2):
            res = True
            break
    memo[key] = res
    return res


def geq(D, D1):
    groups = defaultdict(list)
    for p in D:
        host = None
        for P in D1:
            if all(inside(x, P) for x in p):
                host = P
                break
        if host is None:
            return False
        groups[host].append(p)
    if len(groups) != len(D1):
        return False
    return all(hier(P, frozenset(groups[P])) for P in D1)


def show(D):
    return [list(map(list, t)) for t in sorted(D)]


def ore(N, smax):
    t0 = time.time()
    S = up(frozenset([DELTA]), smax)
    small = sorted([D for D in S if len(D) >= 2], key=lambda D: (len(D), sorted(D)))
    ups = {D: up(D, N) for D in small}
    worst = 0
    fails = []
    hist = defaultdict(int)
    for i in range(len(small)):
        for j in range(i + 1, len(small)):
            I = ups[small[i]] & ups[small[j]]
            if not I:
                fails.append((small[i], small[j]))
                continue
            m = min(len(X) for X in I)
            hist[m] += 1
            worst = max(worst, m)
    print(json.dumps({"mode": "ore", "N": N, "n_small": len(small), "pairs": len(small) * (len(small) - 1) // 2,
                      "pairs_without_common_upper_bound_within_N": len(fails),
                      "min_upper_bound_size_histogram": dict(sorted(hist.items())), "worst": worst,
                      "secs": round(time.time() - t0, 1)}))
    for a, b in fails[:4]:
        print("FAIL", json.dumps({"D1": show(a), "D2": show(b)}))


def spine(N, rounds):
    t0 = time.time()
    atoms = [frozenset(s) for s in splits(DELTA)]
    spine_set = set(atoms)
    cur = list(atoms)
    ups = {}

    def U(D):
        if D not in ups:
            ups[D] = up(D, N)
        return ups[D]

    report = []
    for r in range(rounds):
        new = set()
        truncated = 0
        for i in range(len(cur)):
            for j in range(i + 1, len(cur)):
                I = U(cur[i]) & U(cur[j])
                if not I:
                    truncated += 1
                    continue
                cand = sorted(I, key=len)
                mins = []
                for X in cand:
                    if not any(len(Y) < len(X) and geq(X, Y) for Y in mins):
                        mins.append(X)
                # an element of size N may have smaller minimal bounds outside the window: flag
                for X in mins:
                    if len(X) == N:
                        truncated += 1
                    elif X not in spine_set:
                        new.add(X)
        sizes = defaultdict(int)
        for X in new:
            sizes[len(X)] += 1
        report.append({"round": r + 1, "new": len(new), "new_by_size": dict(sorted(sizes.items())),
                       "truncated_pairs_or_bounds": truncated})
        if not new:
            break
        spine_set |= new
        cur = list(new) + [X for X in spine_set if X not in new]
        cur = sorted(set(cur), key=len)
        if time.time() - t0 > 250:
            report.append({"stopped": "time"})
            break
    sz = defaultdict(int)
    for X in spine_set:
        sz[len(X)] += 1
    print(json.dumps({"mode": "spine", "N": N, "rounds": report, "spine_by_size": dict(sorted(sz.items())),
                      "secs": round(time.time() - t0, 1)}))


def access(N):
    t0 = time.time()
    T = tri((0, 1, 3), (1, 1, 1), (2, 1, 0))
    assert abs(det(*T)) == 1
    S = up(frozenset([DELTA]), N)
    hits = []
    for D in S:
        inT = frozenset(p for p in D if all(inside(x, T) for x in p))
        if not inT:
            continue
        from fractions import Fraction
        w = sum(Fraction(1, sum(p[0]) * sum(p[1]) * sum(p[2])) for p in inT)
        if w == Fraction(1, 4 * 3 * 3) and hier(T, inT):
            hits.append(D)
    print(json.dumps({"mode": "access", "N": N, "n_OE_dissections": len(S), "hits": len(hits),
                      "min_hit_size": min((len(D) for D in hits), default=None),
                      "secs": round(time.time() - t0, 1)}))


if __name__ == "__main__":
    m = sys.argv[1]
    if m == "ore":
        ore(int(sys.argv[2]), int(sys.argv[3]))
    elif m == "spine":
        spine(int(sys.argv[2]), int(sys.argv[3]))
    elif m == "access":
        access(int(sys.argv[2]))
