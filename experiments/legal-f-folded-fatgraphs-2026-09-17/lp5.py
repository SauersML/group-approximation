"""LP search v5: rational legal f-folded fatgraphs as weighted vertex polygons.

A fatgraph X over the rose with boundary = N copies of (w, f(w)^{-1}) is the same as a
multiset of vertex polygons.  A polygon is a cyclic list of slots (d_s -> q_s) with
label(q_s) = inv(label(d_s)) and d_{s+1} = nxt(q_s); the corner preceding d_s sits at
the vertex.  Every condition of the certificate is local to one polygon or one slot:
  legality      directions label(d_s) in pairwise distinct gates
  (2),(3)       at most one f-dart among the d_s, and then the polygon is a 2-gon
  (4)           at most one d^- dart among the d_s; no slot pairs two d^- darts
  no 1-valent   q_s != prv(d_s), nxt(d_s)
LP: weights y_P >= 0; each dart occurs with total weight 1; for each pair {d,q} the
slot weights d->q and q->d agree.  chi per copy = sum_P y_P (1 - k_P/2).  Every
certificate with boundary N copies of (w, f(w)^{-1}) projects to a feasible point, so an
infeasible LP, or min chi = 0, rules out all of them for every N (exact version:
exact_farkas.py).  The converse (realising a rational optimum with chi < 0 as an integral
fatgraph) is NOT implemented; a negative optimum is only a candidate.

usage: python3 lp5.py '<phi json>' m maxlen maxdarts tlimit out.json [words...]
"""
import sys, json, time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from ffold import *
from search3 import power
from search2 import legal_words_dfs


def polygons(B, g, maxval):
    N = B.N
    out = []
    succ = {d: [] for d in range(N)}
    for d in range(N):
        for q in range(N):
            if B.label[q] != inv(B.label[d]) or q in (B.prv[d], B.nxt[d]):
                continue
            if B.kind[d] == "-" and B.kind[q] == "-":
                continue
            succ[d].append((q, B.nxt[q]))

    def rec(darts, slots, gates, nminus, nf):
        d1 = darts[0]; d = darts[-1]; k = len(darts)
        for (q, n) in succ[d]:
            if n == d1:
                if k >= 2 and not (nf and k != 2):
                    out.append(tuple(slots + [(d, q)]))
                continue
            if n <= d1 or k >= maxval:
                continue
            ga = g[B.label[n]]
            if ga in gates:
                continue
            m2 = nminus + (B.kind[n] == "-")
            f2 = nf + B.fdart[n]
            if m2 > 1 or f2 > 1 or (f2 and k >= 2):
                continue
            rec(darts + [n], slots + [(d, q)], gates | {ga}, m2, f2)

    for d1 in range(N):
        rec([d1], [], {g[B.label[d1]]}, int(B.kind[d1] == "-"), int(B.fdart[d1]))
    return out


def solve_lp(B, polys):
    N = B.N
    pairs = {}
    rows, cols, vals = [], [], []
    for j, P in enumerate(polys):
        for (d, q) in P:
            rows.append(d); cols.append(j); vals.append(1.0)
            key = (min(d, q), max(d, q))
            r = pairs.setdefault(key, N + len(pairs))
            rows.append(r); cols.append(j); vals.append(1.0 if d < q else -1.0)
    nrows = N + len(pairs)
    A = coo_matrix((vals, (rows, cols)), shape=(nrows, len(polys))).tocsr()
    b = np.zeros(nrows); b[:N] = 1.0
    c = np.array([1.0 - len(P) / 2.0 for P in polys])
    res = linprog(c, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    return res


def run_word(phi, g, w, maxval):
    B = Boundary(phi, [w])
    polys = polygons(B, g, maxval)
    if not polys:
        return None, B, polys, None
    res = solve_lp(B, polys)
    if res.status == 2:
        return None, B, polys, res
    return res.fun, B, polys, res


def main(phi0, m, maxlen, maxdarts, tlimit, out, words=None):
    phi = power(phi0, m)
    g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    maxval = max(2, 2 * min(gp, gn))
    try:
        cert = certify_fully_irreducible_atoroidal(phi0)
    except Exception as e:
        cert = repr(e)
    print("phi0", phi0, "m", m, "phi", phi, cert, "gates", "".join(g[d] for d in "abcABC"),
          "maxval", maxval, flush=True)
    if words is None:
        words = sorted(legal_words_dfs(g, maxlen, True), key=lambda w: (len(w), w))
    words = [w for w in words if len(w) + len(apply(phi, w)) <= maxdarts]
    print("words", len(words), flush=True)
    t0 = time.time(); stats = {"infeasible": 0, "chi0": 0, "neg": 0}
    best = None
    for w in words:
        chi, B, polys, res = run_word(phi, g, w, maxval)
        if chi is None:
            stats["infeasible"] += 1
        elif chi > -1e-9:
            stats["chi0"] += 1
        else:
            stats["neg"] += 1
            print("NEGATIVE", w, "chi/copy", chi, "darts", B.N, "polygons", len(polys), flush=True)
            if best is None or chi / B.N < best[0]:
                best = (chi / B.N, w, chi)
                support = [[list(s) for s in polys[j]] + [float(res.x[j])]
                           for j in range(len(polys)) if res.x[j] > 1e-9]
                json.dump({"phi0": phi0, "power": m, "phi": phi, "certificate": cert, "w": w,
                           "chi_per_copy": chi, "support": support}, open(out, "w"), indent=1)
        if time.time() - t0 > tlimit:
            print("time limit", flush=True)
            break
    print("stats", stats, "best", best, "time", round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main(json.loads(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
         float(sys.argv[5]), sys.argv[6], sys.argv[7:] or None)
