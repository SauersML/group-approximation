#!/usr/bin/env python3
"""Resonance tests on sums of pencil planes for the braid arrangement (imports os_resonance.py).

Symmetric coordinates: a character of H_n = P_n/Z is c = (c_{st}) on pairs of [n+1] with all row sums zero;
its P_n coordinates are a_{ij} = c_{ij} for i < j <= n. For a subset U of [n+1], L_U = characters supported on
pairs inside U with row sums zero (dim binom(|U|,2) - |U|). |U| = 4 gives the KMM planes.
Usage: python3.11 os_resonance2.py <n> <maxdeg>
"""
import sys, random, itertools
sys.argv = [sys.argv[0], sys.argv[1]] + sys.argv[2:]
import os_resonance as OS

n = OS.n
P = OS.P
MAXDEG = int(sys.argv[2]) if len(sys.argv) > 2 else 2
PTS = list(range(1, n + 2))
PAIRS = [(s, t) for s in PTS for t in PTS if s < t]
PIDX = {p: k for k, p in enumerate(PAIRS)}

def subspace_point(U):
    """Random point of L_U over F_p, returned as a symmetric vector on PAIRS."""
    N = len(PAIRS)
    cons = []
    for k, (s, t) in enumerate(PAIRS):
        if not (s in U and t in U):
            v = [0] * N; v[k] = 1; cons.append(v)
    for s in PTS:
        v = [0] * N
        for k, (x, y) in enumerate(PAIRS):
            if s in (x, y): v[k] = 1
        cons.append(v)
    M = [r[:] for r in cons]; pivcols = []; rk = 0
    for col in range(N):
        piv = next((r for r in range(rk, len(M)) if M[r][col] % P), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][col], P - 2, P); M[rk] = [(x * inv) % P for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col]:
                f = M[r][col]; M[r] = [(x - f * y) % P for x, y in zip(M[r], M[rk])]
        pivcols.append(col); rk += 1
    free = [c for c in range(N) if c not in pivcols]
    c = [0] * N
    for f in free: c[f] = random.randrange(1, P)
    for r, pc in enumerate(pivcols):
        c[pc] = (-sum(M[r][f] * c[f] for f in free)) % P
    return c, len(free)

def to_Pn(c):
    return [c[PIDX[e]] for e in OS.EDGES]

def test(Us):
    tot = [0] * len(PAIRS); dims = []
    for U in Us:
        c, d = subspace_point(U); dims.append(d)
        tot = [(x + y) % P for x, y in zip(tot, c)]
    return OS.aomoto_dims(to_Pn(tot), upto=MAXDEG), dims

if __name__ == "__main__":
    random.seed(7)
    print("n =", n, "H_n points", n + 1, "maxdeg", MAXDEG, flush=True)
    four = [frozenset(U) for U in itertools.combinations(PTS, 4)]
    print("single planes:", test([four[0]]), flush=True)
    if n == 5:
        stats = {}
        for U1, U2 in itertools.combinations(four, 2):
            d, _ = test([U1, U2])
            key = (len(U1 & U2), tuple(d)); stats[key] = stats.get(key, 0) + 1
        print("pairs of planes: (intersection size, H^0..H^maxdeg) -> count", sorted(stats.items()), flush=True)
        stats3 = {}
        for combo in itertools.combinations(four, 3):
            inter = tuple(sorted(len(a & b) for a, b in itertools.combinations(combo, 2)))
            d, _ = test(list(combo))
            key = (inter, tuple(d)); stats3[key] = stats3.get(key, 0) + 1
        print("triples of planes:", sorted(stats3.items()), flush=True)
        five = [frozenset(U) for U in itertools.combinations(PTS, 5)]
        stats5 = {}
        for U5 in five:
            for U4 in four:
                if U4 <= U5: continue
                d, _ = test([U5, U4])
                key = (len(U5 & U4), tuple(d)); stats5[key] = stats5.get(key, 0) + 1
        print("5-set subspace + plane:", sorted(stats5.items()), flush=True)
    if n == 6:
        cases = {
            "two disjoint triples {123},{456} (core 7)": [frozenset({1, 2, 3, 7}), frozenset({4, 5, 6, 7})],
            "pair meeting in 2: {1234},{3456}": [frozenset({1, 2, 3, 4}), frozenset({3, 4, 5, 6})],
            "pair meeting in 2: {1234},{3457}": [frozenset({1, 2, 3, 4}), frozenset({3, 4, 5, 7})],
            "5-set {12345} + plane {4567}": [frozenset({1, 2, 3, 4, 5}), frozenset({4, 5, 6, 7})],
            "5-set {12345} + plane {5,6,7,1}": [frozenset({1, 2, 3, 4, 5}), frozenset({1, 5, 6, 7})],
            "three planes {1234},{3456},{5612}": [frozenset({1, 2, 3, 4}), frozenset({3, 4, 5, 6}), frozenset({5, 6, 1, 2})],
            "6-set {123456}": [frozenset({1, 2, 3, 4, 5, 6})],
        }
        for name, Us in cases.items():
            print(f"{name:45s}", test(Us), flush=True)
    print("DONE")
