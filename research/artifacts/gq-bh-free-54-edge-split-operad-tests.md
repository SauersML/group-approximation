# Edge-split operad on the cone in R^3: Ore, chain and accessibility tests

This artifact supports Attempt 2 of `edge-split-operad-satisfies-ore` and part 4 of
`transvections-are-single-carets-of-the-edge-split-operad`. Lane bh-free-54,
2026-09-18. It ran on MSI (acn112) on a few cores for minutes; nothing was run
locally.

## Incomparable-row unimodular matrices (`rows.py`)

A row triple counted here gives a unimodular cone in no half of any first edge
split, and so a non-node. Both counts include the permutation matrix.

```
{"K": 3, "incomparable_unimodular_row_triples": 73, first non-permutation example rows [[0,1,2],[1,1,1],[3,1,0]]}
{"K": 5, "incomparable_unimodular_row_triples": 2389}
```

## Ore brute force, spine lower bound, accessibility of the non-node (`ore.py`)

```
== ore84.out
{"mode": "ore", "N": 8, "n_small": 156, "pairs": 12090, "pairs_without_common_upper_bound_within_N": 7266, "min_upper_bound_size_histogram": {"3": 18, "4": 324, "5": 948, "6": 1710, "7": 1014, "8": 810}, "worst": 8, "secs": 53.0}
FAIL {"D1": [[[0, 0, 1], [0, 1, 0], [1, 0, 1]], [[0, 1, 0], [1, 0, 0], [1, 0, 1]]], "D2": [[[0, 0, 1], [0, 1, 0], [1, 1, 0]], [[0, 0, 1], [1, 0, 0], [2, 1, 0]], [[0, 0, 1], [1, 1, 0], [2, 1, 0]]]}
== spine9.out
{"mode": "spine", "N": 9, "rounds": [{"round": 1, "new": 6, "new_by_size": {"5": 6}, "truncated_pairs_or_bounds": 0}, {"round": 2, "new": 7, "new_by_size": {"6": 1, "7": 3, "8": 3}, "truncated_pairs_or_bounds": 3}, {"round": 3, "new": 0, "new_by_size": {}, "truncated_pairs_or_bounds": 27}], "spine_by_size": {"2": 3, "5": 6, "6": 1, "7": 3, "8": 3}, "secs": 234.8}
== access9.out
{"mode": "access", "N": 9, "n_OE_dissections": 10060001, "hits": 0, "min_hit_size": null, "secs": 261.9}
```

## Barycentric chain cofinality (`chain.py`)

```
{"K": 4, "sizes": [1, 6, 36, 216, 1296], "small_max": 5, "n_small": 1284, "min_k_with_Uk_geq_D": {"1": 21, "2": 240, "3": 399, "4": 84, "None": 540}, "selfsim_half_E01": {"1": 0, "2": 0, "3": 1, "4": 1}, "selfsim_quarter": {"1": 0, "2": 0, "3": 0, "4": 0}}
{"K": 5, "sizes": [1, 6, 36, 216, 1296, 7776], "small_max": 4, "n_small": 156, "min_k_with_Uk_geq_D": {"1": 18, "2": 45, "3": 57, "None": 36}, "selfsim_half_E01": {"1": 0, "2": 0, "3": 1, "4": 1, "5": 1}, "selfsim_quarter": {"1": 0, "2": 0, "3": 0, "4": 0, "5": 0}}
```

## Scripts

### `rows.py`

```python
# Nonnegative 3x3 integer matrices with det +-1 whose rows are pairwise incomparable.
# Such a matrix = a unimodular cone (columns) lying in no half of any edge split of Delta.
import sys, itertools, json
K = int(sys.argv[1])
V = [v for v in itertools.product(range(K + 1), repeat=3) if any(v)]
def leq(a, b): return all(x <= y for x, y in zip(a, b))
def comp(a, b): return leq(a, b) or leq(b, a)
def det(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0]))
n = len(V); bad = []; unimod = 0
for i in range(n):
    a = V[i]
    for j in range(i + 1, n):
        b = V[j]
        if comp(a, b): continue
        cr = (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
        for k in range(j + 1, n):
            c = V[k]
            d = cr[0]*c[0] + cr[1]*c[1] + cr[2]*c[2]
            if d != 1 and d != -1: continue
            if comp(a, c) or comp(b, c): continue
            bad.append((a, b, c))
print(json.dumps({"K": K, "incomparable_unimodular_row_triples": len(bad), "examples": bad[:12]}))
```

### `ore.py`

```python
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
```

### `chain.py`

```python
# Is the iterated barycentric edge-split chain U_k cofinal in the O_E order?
import sys, json, time
from ore import *
sys.setrecursionlimit(10000)
def B6(t):
    a, b, d = t
    z = add(add(a, b), d); mab, mbd, mad = add(a, b), add(b, d), add(a, d)
    return [tri(a, mab, z), tri(mab, b, z), tri(b, mbd, z), tri(mbd, d, z), tri(d, mad, z), tri(mad, a, z)]
K = int(sys.argv[1]); SM = int(sys.argv[2])
t0 = time.time()
U = [frozenset([DELTA])]
for k in range(K):
    U.append(frozenset(p for t in U[-1] for p in B6(t)))
assert all(hier(DELTA, U[k]) for k in range(1, min(K, 3) + 1)), "U_k not in O_E"
small = [D for D in up(frozenset([DELTA]), SM) if len(D) >= 2]
need = {}
for D in small:
    kk = None
    for k in range(1, K + 1):
        if geq(U[k], D):
            kk = k; break
    need[kk] = need.get(kk, 0) + 1
# self-similarity: pull U_k back from the half H=(e0,v01,e2) of E_01 and from the half-of-half
def pullback(frame, pieces):
    a, b, d = frame
    import fractions
    M = [[a[0], b[0], d[0]], [a[1], b[1], d[1]], [a[2], b[2], d[2]]]
    D = det(a, b, d)
    def solve(x):  # coordinates of x in basis (a,b,d)
        return (det(x, b, d) // D, det(a, x, d) // D, det(a, b, x) // D)
    return frozenset(tri(*[solve(x) for x in p]) for p in pieces)
out = {"mode": "chain", "K": K, "sizes": [len(u) for u in U], "small_max": SM, "n_small": len(small),
       "min_k_with_Uk_geq_D": {str(k): v for k, v in sorted(need.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))}}
for name, H in (("half_E01", tri(E0, (1, 1, 0), E2)), ("quarter", tri(E0, (2, 1, 0), E2))):
    res = {}
    for k in range(1, K + 1):
        inH = frozenset(p for p in U[k] if all(inside(x, H) for x in p))
        pb = pullback(H, inH)
        best = 0
        for kp in range(1, k + 1):
            if geq(pb, U[kp]): best = kp
        res[k] = best
    out["selfsim_" + name] = res
out["secs"] = round(time.time() - t0, 1)
print(json.dumps(out))
```
