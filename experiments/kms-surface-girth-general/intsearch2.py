#!/usr/bin/env python3
"""Integer labellings of KMS girth surfaces with |labels| <= N, closed words enumerated by the moment lemma
(lane hl-surface-girth-general, 2026-09-14).

Moment lemma: an alternating word x^{a_1} y^{b_1} ... x^{a_m} y^{b_m} is trivial in U_3 (m = 3) or U_4 (m = 4,
x designated) exactly when sum b = 0 and sum_r a_r H_r^d = 0 for 0 <= d <= m-2, where H_r = b_1 + ... + b_{r-1}.
Closed words are generated from heights and checked again with the normal-form law of kms_girth_search.word_trivial.

usage: intsearch2.py FAMILY T N i,j,...|all OUT.json
Optional env KMS_ABS=1,2,4,8 restricts label absolute values (applied after enumeration); the search
stops at the first labelling per surface and reports progress per surface.
"""
import sys, json, time, os
from fractions import Fraction
from itertools import product
from math import gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kms_girth_search as K
import explore as E

PAIR = K.PAIR
ALLOWED = set(int(x) for x in os.environ["KMS_ABS"].split(",")) if os.environ.get("KMS_ABS") else set(range(1, 10 ** 6))


def closed_x_first(m, N):
    """(a, b) with x-exponents a, y-exponents b in [-N,N]\\0, word x^a1 y^b1 ... trivial."""
    out = set()
    rng = [v for v in range(-N, N + 1) if v]
    for bs in product(rng, repeat=m - 1):
        last = -sum(bs)
        if last == 0 or abs(last) > N: continue
        b = bs + (last,)
        H = [0]
        for s in range(m - 1): H.append(H[-1] + b[s])
        distinct = len(set(H)) == m
        cands = []
        if distinct:
            w = []
            for r in range(m):
                den = 1
                for s in range(m):
                    if s != r: den *= (H[r] - H[s])
                w.append(Fraction(1, den))
            L = 1
            for x in w: L = L * x.denominator // gcd(L, x.denominator)
            v = [int(x * L) for x in w]
            g = 0
            for x in v: g = gcd(g, abs(x))
            v = [x // g for x in v]
            mx = max(abs(x) for x in v)
            for lam in range(-(N // mx), N // mx + 1):
                if lam: cands.append(tuple(lam * x for x in v))
        elif m == 4 and H[0] == H[2] and H[1] == H[3]:
            for a1 in rng:
                for a2 in rng: cands.append((a1, a2, -a1, -a2))
        for a in cands:
            if all(a) and max(abs(x) for x in a) <= N and all(abs(x) in ALLOWED for x in a + b): out.add((a, b))
    return out


WC = {}
def closed_words(i, m, kind, N):
    key = (i, m, kind, N)
    if key in WC: return WC[key]
    types = [PAIR[i][q & 1] for q in range(2 * m)]
    xk = types[0] if kind[0] == "U3" else kind[1]
    words = set()
    for (a, b) in closed_x_first(m, N):
        if xk == types[0]:
            w = [0] * (2 * m); w[0::2] = a; w[1::2] = b
        else:                      # x at odd positions: y^{b_m} x^{a_1} y^{b_1} ... is a cyclic rotation
            w = [0] * (2 * m); w[1::2] = a; w[2::2] = b[:-1]; w[0] = b[-1]
        w = tuple(w)
        assert K.word_trivial(kind, [(types[q], w[q]) for q in range(2 * m)])
        words.add(w)
    WC[key] = sorted(words)
    return WC[key]


def solve(N, nE, verts, vm, vf, limit):
    occ_of = [[] for _ in range(nE)]
    for v, (i, occ) in enumerate(verts):
        for (e, sg, q) in occ: occ_of[e].append((v, sg, q))
    vals = [x for x in range(-N, N + 1) if x and abs(x) in ALLOWED]
    dom = list(vf); assign = [0] * nE; sols = []

    def vals_of(e):
        out = []
        for x in vals:
            ds = []
            for (v, sg, q) in occ_of[e]:
                a = dom[v] & vm[v][q].get(sg * x, 0)
                if not a: break
                ds.append((v, a))
            else:
                out.append((x, ds))
        return out

    def dfs(depth):
        if depth == nE: sols.append(list(assign)); return
        best = None; bvals = None
        for e in range(nE):
            if assign[e]: continue
            vs = vals_of(e)
            if not vs: return
            if best is None or len(vs) < len(bvals):
                best, bvals = e, vs
                if len(vs) == 1: break
        saved = [(v, dom[v]) for (v, _, _) in occ_of[best]]
        for (x, ds) in bvals:
            assign[best] = x
            for v, a in ds: dom[v] = a
            dfs(depth + 1)
            for v, a in saved: dom[v] = a
            if len(sols) >= limit: break
        assign[best] = 0
    dfs(0)
    return sols


def main():
    fam, T, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    out = sys.argv[5]
    M, kinds = K.FAMILIES[fam]; t0 = time.time()
    S = K.surfaces(T, M)
    idxs = list(range(len(S))) if sys.argv[4] == "all" else [int(x) for x in sys.argv[4].split(",")]
    print("girth surfaces", len(S), "allowed abs", sorted(ALLOWED)[:12], flush=True)
    for i in range(3):
        print("type", i, kinds[i], "closed words with |exp| <=", N, ":", len(closed_words(i, M[i], kinds[i], N)), flush=True)
    report = {"family": fam, "half_girths": list(M), "T": T, "N": N, "surfaces": len(S), "certificates": []}
    for n in idxs:
        r = S[n]; edges, verts = E.structure(r, T, M)
        vm, vf = [], []
        for v, (i, occ) in enumerate(verts):
            W = closed_words(i, M[i], kinds[i], N)
            ms = [dict() for _ in range(2 * M[i])]
            for idx, w in enumerate(W):
                for q, x in enumerate(w): ms[q][x] = ms[q].get(x, 0) | (1 << idx)
            vm.append(ms); vf.append((1 << len(W)) - 1)
        sols = solve(N, len(edges), verts, vm, vf, 1)
        print("surface", n, "orientable", K.orientable(r, T), "integer labelling found", bool(sols), "sec",
              round(time.time() - t0, 1), flush=True)
        for sol in sols:
            report["certificates"].append({"surface_index": n, "orientable": K.orientable(r, T), "T": T,
                                           "r0": r[0], "r1": r[1], "r2": r[2],
                                           "labels": [[k, t, s, sol[e]] for e, (k, t, s) in enumerate(edges)]})
    json.dump(report, open(out, "w"))
    print("done sec", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
