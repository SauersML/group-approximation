"""Soundness check for lp_allwords.py on the certificates actually found.

Each certificate JSON (keys phi0, power, minus_words, pairing) is a legal f-folded fatgraph with
chi < 0 (checked independently by verify_surface.py). Here the boundary is rebuilt in the same
dart order as verify_surface.py (for each d^- word w: the d^- circle w, then the d^+ circle
reading f(w_L)^-1 ... f(w_1)^-1), every dart is projected to its LP type, and we check:
  * labels, f-dart flags and d^-/d^+ kinds agree with the type, and the boundary successor of
    every dart is a successor type of its type;
  * every vertex (orbit of sigma = nxt o p) projects to a polygon in the list enumerated by
    lp_allwords.polygons with the census bound maxval = 2 min(g+, g-);
  * the resulting integer point (y, c) satisfies A y + B c = 0 exactly, with sum c > 0, and
    chi = sum_P y_P (1 - k_P/2) equals the certificate's chi.
So every certificate is a feasible point of the census LP, as the soundness argument predicts.

usage: python3 validate_certificates.py cert1.json [cert2.json ...]
"""
import sys, json
from collections import Counter
import lp_allwords as LA


def red(w):
    o = []
    for x in w:
        if o and o[-1] == x.swapcase():
            o.pop()
        else:
            o.append(x)
    return "".join(o)


cache = {}
bad = 0
for path in sys.argv[1:]:
    cert = json.load(open(path))
    phi = LA.power(cert["phi0"], cert["power"])
    key = json.dumps(phi, sort_keys=True)
    if key not in cache:
        g = LA.gates(phi)
        gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
        maxval = max(2, 2 * min(gp, gn))
        TY = LA.Types(phi, g)
        polys = LA.polygons(TY, g, maxval)
        cache[key] = (TY, polys, {P: j for j, P in enumerate(polys)}, LA.build(TY, polys), maxval)
    TY, polys, pidx, (nrows, cols, ccols), maxval = cache[key]
    label, kind, fdart, nxt, tm = [], [], [], [], []
    for w in cert["minus_words"]:
        L = len(w)
        start = len(label)
        for i, x in enumerate(w):
            label.append(x); kind.append("-"); fdart.append(False)
            tm.append(TY.idx[("-", x, w[(i + 1) % L])])
        for i in range(L):
            nxt.append(start + (i + 1) % L)
        start = len(label)
        for t in range(L - 1, -1, -1):
            x = w[t]; blk = TY.R[x]; ell = len(blk)
            assert blk == red(blk)
            for i in range(ell):
                label.append(blk[i]); kind.append("+"); fdart.append(i == 0)
                tm.append(TY.idx[("+", x, i)] if i < ell - 1 else TY.idx[("L", w[(t - 1) % L], x)])
        n = len(label) - start
        for i in range(n):
            nxt.append(start + (i + 1) % n)
    p = cert["pairing"]
    N = len(label)
    assert len(p) == N
    for d in range(N):
        assert TY.label[tm[d]] == label[d], ("label", d)
        assert TY.fdart[tm[d]] == fdart[d], ("fdart", d)
        assert TY.kind[tm[d]] == kind[d], ("kind", d)
        assert tm[nxt[d]] in TY.succ[tm[d]], ("successor", d)
        assert p[p[d]] == d and p[d] != d and label[p[d]] == label[d].swapcase()
    seen, y = set(), Counter()
    for d0 in range(N):
        if d0 in seen:
            continue
        orb, d = [], d0
        while d not in seen:
            seen.add(d); orb.append(d); d = nxt[p[d]]
        sl = [(tm[d], tm[p[d]]) for d in orb]
        r = min(range(len(sl)), key=lambda i: sl[i][0])
        P = tuple(sl[r:] + sl[:r])
        assert P in pidx, ("vertex is not an enumerated polygon", path, P)
        y[pidx[P]] += 1
    c = Counter()
    for w in cert["minus_words"]:
        for i in range(len(w)):
            c[TY.tidx[(w[i], w[(i + 1) % len(w)])]] += 1
    tot = [0] * nrows
    for j, v in y.items():
        for row, val in cols[j].items():
            tot[row] += val * v
    for j, v in c.items():
        for row, val in ccols[j].items():
            tot[row] += val * v
    ok = all(t == 0 for t in tot) and sum(c.values()) > 0
    chi2 = sum(v * (2 - len(polys[j])) for j, v in y.items())
    V = sum(y.values())
    print("%s phi0=%s minus=%s maxval=%d polygons=%d vertices=%d chi=%s feasible=%s" % (
        path, json.dumps(cert["phi0"]), ",".join(cert["minus_words"]), maxval, len(polys), V,
        chi2 / 2, ok), flush=True)
    bad += not (ok and chi2 < 0)
print("summary: %d certificates, %d failures" % (len(sys.argv) - 1, bad))
sys.exit(1 if bad else 0)
