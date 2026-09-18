"""Exact realisation of the per-word polygon LP (lp5.py) up to finite covers.

Boundary B = Boundary(phi, W) for a list W of candidate d^- words (each with its d^+ circle
f(w)^{-1}).  Variables: integers y_P >= 0 (vertex polygons of lp5.polygons) and n_w >= 0 (copies of
word w).  Rows: every dart of the two circles of w is covered n_w times; slot weights d->q and q->d
agree; chi = sum_P y_P (1 - |P|/2) <= -1.

Realisation (the converse lp5.py does not implement):
 1. positions = (polygon copy, slot); p pairs the positions of slot (d->q) with those of slot (q->d),
    nxt(p(x)) = next position of x in its polygon.  Vertex cycles nxt o p are the chosen polygons, so
    (L), (2), (3), (4) hold, and nxt covers nxt_B on dart types: every boundary circle is a k-fold
    cover of a circle of B.  Sum of k over the d^- circles over w = n_w = same sum over d^+ circles.
 2. Z/K cover with circle monodromy +k u (d^-) resp. -k u (d^+), u a unit mod K/k, summing to 0 on
    every component of X: every lifted circle reads w^K resp. f(w^K)^{-1}; numbers agree per w.
 3. Match, restrict to one component of S*_f(X) with chi < 0, write certificate, run the checkers.

usage: python3 lift_word.py '<phi0 json>' m out.json word [word ...] [--seed S] [--tries T] [--cmax M]
       [--copies K] (first MILP with sum n_w = K) [--connected] (retry while the base fatgraph is disconnected)
"""
import sys, json, os, random, subprocess, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix, csr_matrix
from ffold import Boundary, gate_of, inv, inv_word, apply
from search3 import power
import lp5
from lift_lp import positions_fatgraph, circles_of, x_components, cover_monodromies, lift


def int_solution(B, W, polys, rng, tl=900, K=None, ymax=60):
    N = B.N
    nP, nW = len(polys), len(W)
    nv = nP + nW
    circ_word = [B.circle[d][0] for d in range(N)]
    rows, cols, vals = [], [], []
    pairs = {}
    for j, P in enumerate(polys):
        for (d, q) in P:
            rows.append(d); cols.append(j); vals.append(1.0)
            key = (min(d, q), max(d, q))
            r = pairs.setdefault(key, N + len(pairs))
            rows.append(r); cols.append(j); vals.append(1.0 if d < q else -1.0)
    for d in range(N):
        rows.append(d); cols.append(nP + circ_word[d]); vals.append(-1.0)
    A = coo_matrix((vals, (rows, cols)), shape=(N + len(pairs), nv)).tocsr()
    chi = np.zeros(nv); chi[:nP] = [1.0 - len(P) / 2.0 for P in polys]
    cons = [LinearConstraint(A, 0, 0), LinearConstraint(csr_matrix(chi), -np.inf, -1)]
    obj = np.zeros(nv)
    if K is None:
        obj[nP:] = [len(W[i]) for i in range(nW)]
    else:
        row = np.zeros(nv); row[nP:] = 1
        cons.append(LinearConstraint(csr_matrix(row), K, K))
        obj[:nP] = [rng.random() for _ in range(nP)]
    ub = np.full(nv, float(ymax))
    res = milp(obj, constraints=cons, integrality=np.ones(nv), bounds=Bounds(0, ub),
               options={"time_limit": tl, "disp": False})
    if res.x is None:
        return None, None, res
    x = np.round(res.x).astype(int)
    y = {j: int(x[j]) for j in range(nP) if x[j] > 0}
    n = {W[i]: int(x[nP + i]) for i in range(nW) if x[nP + i] > 0}
    return y, n, res


def circle_info_B(B, typ, o):
    d0 = typ[o[0]]
    ci, kind = B.circle[d0]
    L = sum(1 for d in range(B.N) if B.circle[d] == (ci, kind))
    assert len(o) % L == 0
    return kind, ci, len(o) // L


def matched_certificate_B(B, typ, p, nxt):
    circ = circles_of(nxt)
    minus, plus = {}, {}
    start = {}
    for d in range(B.N):
        key = B.circle[d]
        start.setdefault(key, d)          # first dart of each B circle
    for o in circ:
        kind, ci, k = circle_info_B(B, typ, o)
        (minus if kind == "-" else plus).setdefault(ci, []).append(o)
    assert {k: len(v) for k, v in minus.items()} == {k: len(v) for k, v in plus.items()}, \
        ("unmatched", {k: len(v) for k, v in minus.items()}, {k: len(v) for k, v in plus.items()})
    order, words = [], []
    for ci in sorted(minus):
        for om, op in zip(minus[ci], plus[ci]):
            s = next(i for i, x in enumerate(om) if typ[x] == start[(ci, "-")])
            om = om[s:] + om[:s]
            s = next(i for i, x in enumerate(op) if typ[x] == start[(ci, "+")])
            op = op[s:] + op[:s]
            w = "".join(B.label[typ[x]] for x in om)
            assert "".join(B.label[typ[x]] for x in op) == inv_word(apply(B.phi, w))
            order.extend(om); order.extend(op); words.append(w)
    ren = {a: i for i, a in enumerate(order)}
    pairing = [ren[p[a]] for a in order]
    labels = [B.label[typ[a]] for a in order]
    return words, labels, pairing


def restrict(words, labels, pairing, phi):
    Nw = len(labels)
    circles = []; pos = 0
    for w in words:
        circles.append((pos, len(w))); pos += len(w)
        pl = len(apply(phi, w))
        circles.append((pos, pl)); pos += pl
    assert pos == Nw
    nx = [0] * Nw
    for s0, L in circles:
        for i in range(L):
            nx[s0 + i] = s0 + (i + 1) % L
    par = list(range(Nw))
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for d in range(Nw):
        for e in (pairing[d], nx[pairing[d]]):
            par[f(d)] = f(e)
    for ci in range(0, len(circles), 2):
        par[f(circles[ci][0])] = f(circles[ci + 1][0])
    groups = {}
    for d in range(Nw):
        groups.setdefault(f(d), []).append(d)
    best = None
    for rt, ds in groups.items():
        V = 0; seen = set()
        for d in ds:
            if d not in seen:
                e = d
                while e not in seen:
                    seen.add(e); e = nx[pairing[e]]
                V += 1
        chi_c = V - len(ds) // 2
        if chi_c < 0 and (best is None or len(ds) < len(best[1])):
            best = (chi_c, ds)
    if best is None:
        return None
    keep = set(best[1])
    new_words, order = [], []
    for i, w in enumerate(words):
        s0, L = circles[2 * i]
        if s0 in keep:
            new_words.append(w)
            order.extend(range(s0, s0 + L))
            s1, L1 = circles[2 * i + 1]
            order.extend(range(s1, s1 + L1))
    ren = {a: i for i, a in enumerate(order)}
    return (len(groups), best[0], new_words, [labels[a] for a in order], [ren[pairing[a]] for a in order])


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--seed", "--tries", "--cmax", "--maxval", "--copies"):
        if key in args:
            i = args.index(key); opts[key] = int(args[i + 1]); del args[i:i + 2]
    args = [a for a in args if a != "--connected"]
    phi0 = json.loads(args[0]); m = int(args[1]); out = args[2]; W = args[3:]
    rng = random.Random(opts.get("--seed", 1))
    t0 = time.time()
    phi = power(phi0, m)
    g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    maxval = opts.get("--maxval", max(2, 2 * min(gp, gn)))
    B = Boundary(phi, W)
    polys = lp5.polygons(B, g, maxval)
    print("words", W, "darts", B.N, "polygons", len(polys), "maxval", maxval, "t", round(time.time() - t0, 1),
          flush=True)
    if not polys:
        print("no polygons"); sys.exit(2)
    lpres = lp5.solve_lp  # noqa (LP relaxation reported by lp5.py per single word)
    tries = opts.get("--tries", 6)
    base = None
    for t in range(tries):
        K = (opts.get("--copies") if t == 0 else base * (1 + (t - 1) // 2))
        y, n, res = int_solution(B, W, polys, rng, K=K, ymax=opts.get("--cmax", 60))
        if y is None:
            print("MILP: no integer solution", K, res.status, res.message, flush=True)
            if t == 0:
                sys.exit(2)
            continue
        if base is None:
            base = sum(n.values())
        if len(set(x_components(*positions_fatgraph(None, polys, y, random.Random(0))[1:3]))) > 1 and t + 1 < tries and "--connected" in sys.argv:
            print("try", t, "base fatgraph disconnected, retrying", flush=True); continue
        chi = sum(v * (1 - len(polys[j]) / 2) for j, v in y.items())
        print("try", t, "copies", n, "chi", chi, "vertices", sum(y.values()), "t", round(time.time() - t0, 1),
              flush=True)
        typ, p, nxt, sigma = positions_fatgraph(None, polys, y, rng)
        Np = len(typ)
        for x in range(Np):
            assert typ[nxt[x]] == B.nxt[typ[x]], "nxt does not cover nxt_B"
            assert B.label[typ[p[x]]] == inv(B.label[typ[x]])
            assert nxt[p[x]] == sigma[x]
        circ = circles_of(nxt)
        info = [circle_info_B(B, typ, o) for o in circ]
        cx = x_components(p, nxt)
        print("base darts", Np, "X components", len(set(cx)), "circles (kind, word, k)",
              [(kd, W[ci], k) for kd, ci, k in info], flush=True)
        Kc, mono = cover_monodromies(info, [cx[o[0]] for o in circ], rng)
        if Kc is None:
            print("no cyclic cover found", flush=True)
            continue
        break
    else:
        print("giving up", flush=True); sys.exit(4)
    typ2, p2, nxt2 = lift(None, typ, p, nxt, Kc, mono)
    print("cover degree", Kc, "monodromies", mono, "cover darts", len(typ2), flush=True)
    words, labels, pairing = matched_certificate_B(B, typ2, p2, nxt2)
    r = restrict(words, labels, pairing, phi)
    if r is None:
        print("no S* component with chi < 0"); sys.exit(4)
    ncomp, chic, words, labels, pairing = r
    print("S* components", ncomp, "chosen chi", chic, "minus words", len(words), flush=True)
    cert = {"phi0": phi0, "power": m, "phi": phi, "minus_words": words, "labels": labels, "pairing": pairing,
            "construction": "lift_word.py words %s seed %d cover %d" % (W, opts.get("--seed", 1), Kc),
            "milp_copies": n,
            "milp_polygons": [[v, [[d, q] for d, q in polys[j]]] for j, v in sorted(y.items())]}
    json.dump(cert, open(out, "w"))
    here = os.path.dirname(os.path.abspath(__file__))
    rc = 5
    for chk in ("verify_surface.py", "verify_surface_multi.py"):
        rr = subprocess.run(["python3", os.path.join(here, chk), out], capture_output=True, text=True)
        print(chk, rr.stdout.strip()[:700], rr.stderr.strip()[-300:], flush=True)
        if rr.returncode == 0:
            rc = 0
    sys.exit(rc)


if __name__ == "__main__":
    main()
