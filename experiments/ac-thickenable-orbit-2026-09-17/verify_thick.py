#!/usr/bin/env python3
"""Independent brute-force Neuwirth test (no pruning), for cross-checking libthick.so.
Link graph: vertices (g,'o'),(g,'i'); each occurrence k of g^{+-1} owns one half-edge at
(g,'o') and one at (g,'i').  Corner j of relator r is an edge from end(a_j) [half-edge of
occurrence j] to start(a_{j+1}) [half-edge of occurrence j+1].  Rotation at (g,'o') is a
cyclic order sigma_g of the occurrences of g, rotation at (g,'i') is sigma_g^{-1}.
Faces = cycles of rot o twin.  Planar iff V - E + F = 2 * (#components).
Exhaustive over all sigma_g.  Usage: verify_thick.py r1 r2 ...
"""
import sys, itertools

def check(rels):
    occ = []  # (gen, sign)
    base = []
    for r in rels:
        base.append(len(occ))
        for ch in r:
            occ.append((ch.lower(), 1 if ch.islower() else -1))
    gens = sorted({g for g, _ in occ})
    # half-edge id: (occ k, side)  side 'o' or 'i'
    def start(k):
        return 'o' if occ[k][1] == 1 else 'i'
    def end(k):
        return 'i' if occ[k][1] == 1 else 'o'
    twin = {}
    for ri, r in enumerate(rels):
        L = len(r)
        for j in range(L):
            k1, k2 = base[ri] + j, base[ri] + (j + 1) % L
            h1, h2 = (k1, end(k1)), (k2, start(k2))
            twin[h1] = h2; twin[h2] = h1
    V = {(occ[k][0], s) for (k, s) in twin}
    par = {v: v for v in V}
    def f(v):
        while par[v] != v:
            v = par[v]
        return v
    for (k, s), (k2, s2) in twin.items():
        par[f((occ[k][0], s))] = f((occ[k2][0], s2))
    c = len({f(v) for v in V})
    E = len(twin) // 2
    byg = {g: [k for k in range(len(occ)) if occ[k][0] == g] for g in gens}
    choices = []
    for g in gens:
        ks = byg[g]
        choices.append([(ks[0],) + p for p in itertools.permutations(ks[1:])])
    for combo in itertools.product(*choices):
        rot = {}
        for cyc in combo:
            n = len(cyc)
            for i in range(n):
                rot[(cyc[i], 'o')] = (cyc[(i + 1) % n], 'o')
                rot[(cyc[(i + 1) % n], 'i')] = (cyc[i], 'i')
        seen = set(); F = 0
        for h in twin:
            if h in seen:
                continue
            F += 1; x = h
            while x not in seen:
                seen.add(x); x = rot[twin[x]]
        if len(V) - E + F == 2 * c:
            return True, combo
    return False, None

if __name__ == "__main__":
    ok, w = check(sys.argv[1:])
    print(ok, sys.argv[1:], w)
