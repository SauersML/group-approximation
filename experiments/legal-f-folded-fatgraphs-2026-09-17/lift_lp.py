"""Lift an integer solution of the word-free LP (lp_allwords.py) to a legal f-folded fatgraph
certificate, via the position construction plus a finite cyclic cover.

1. MILP: integer y (vertex polygons) and c (turn counts) solving the LP system with chi <= -1.
   With --perm the turn support is forced to be a partial permutation of the letters
   (each letter has at most one legal successor in the support).
2. Positions = (polygon copy, slot).  pi = type-respecting fixed-point-free involution between
   positions of slot (d->q) and slot (q->d) (pair rows = equal numbers).  nxt(pi(x)) = next position
   of x in its polygon, p = pi.  Then vertex cycles nxt o p are exactly the chosen polygons, so
   (L), (2), (3), (4) hold; boundary circles are type-legal sequences: d^- circles read cyclic legal
   words, d^+ circles read complete blocks R(x_L)...R(x_1).  Components are merged by edge swaps.
3. Permutation support: every d^- circle reads u^k and every d^+ circle reads f(u^l)^{-1} for
   cycles u of the successor permutation, with sum k = sum l per cycle u (type-count rows).
4. Cyclic cover of degree K = lcm(k's): edge voltages g with boundary monodromy +k on d^- circles,
   -k on d^+ circles (total 0, solved on a spanning tree of the circle-adjacency graph).  Every lifted
   circle reads u^K resp. f(u^K)^{-1}, numbers agree per u, so the lifted boundary is matched.
5. Write the certificate in the verify_surface.py format and run the independent checker.

usage: python3 lift_lp.py '<phi0 json>' m out.json [--perm] [--seed S] [--cmax M]
"""
import sys, json, os, random, subprocess, time
from math import gcd
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix, csr_matrix, vstack
import lp_allwords as LA
from ffold import inv


def int_solution(TY, polys, perm, cmax=60, tl=900, K=None, rng=None):
    nrows, cols, ccols = LA.build(TY, polys)
    ny, nc = len(cols), len(ccols)
    nz = nc if perm else 0
    nv = ny + nc + nz
    r, c, v = [], [], []
    for j, col in enumerate(cols):
        for row, val in col.items():
            r.append(row); c.append(j); v.append(val)
    for j, col in enumerate(ccols):
        for row, val in col.items():
            r.append(row); c.append(ny + j); v.append(val)
    A = coo_matrix((v, (r, c)), shape=(nrows, nv)).tocsr()
    chi = np.zeros(nv)
    chi[:ny] = [1.0 - len(P) / 2.0 for P in polys]
    cons = [LinearConstraint(A, 0, 0), LinearConstraint(csr_matrix(chi), -np.inf, -1)]
    ub = np.full(nv, np.inf)
    ub[ny:ny + nc] = cmax
    if perm:
        ub[ny + nc:] = 1
        rows = []
        for j in range(nc):                       # c_j <= cmax z_j
            row = np.zeros(nv); row[ny + j] = 1; row[ny + nc + j] = -cmax
            rows.append(row)
        M1 = csr_matrix(np.array(rows))
        cons.append(LinearConstraint(M1, -np.inf, 0))
        rows = []
        for x in TY.L:                            # at most one successor per letter
            row = np.zeros(nv)
            for j, t in enumerate(TY.turns):
                if t[0] == x:
                    row[ny + nc + j] = 1
            rows.append(row)
        cons.append(LinearConstraint(csr_matrix(np.array(rows)), -np.inf, 1))
    obj = np.zeros(nv); obj[ny:ny + nc] = 1
    if K is not None:
        row = np.zeros(nv); row[ny:ny + nc] = 1
        cons.append(LinearConstraint(csr_matrix(row), K, K))
        obj = np.zeros(nv); obj[:ny] = [rng.random() for _ in range(ny)]
    res = milp(obj, constraints=cons, integrality=np.ones(nv), bounds=Bounds(0, ub),
               options={"time_limit": tl, "disp": False})
    if res.x is None:
        return None, None, res
    x = np.round(res.x).astype(int)
    y = {j: int(x[j]) for j in range(ny) if x[j] > 0}
    cnt = {TY.turns[j]: int(x[ny + j]) for j in range(nc) if x[ny + j] > 0}
    return y, cnt, res


def positions_fatgraph(TY, polys, y, rng):
    pos = []           # (poly index, copy, slot)
    sigma = []
    for j, n in sorted(y.items()):
        P = polys[j]
        for cp in range(n):
            base = len(pos)
            for s in range(len(P)):
                pos.append((j, cp, s))
            for s in range(len(P)):
                sigma.append(base + (s + 1) % len(P))
    N = len(pos)
    typ = [polys[j][s][0] for (j, cp, s) in pos]
    part = [polys[j][s][1] for (j, cp, s) in pos]
    groups = {}
    for x in range(N):
        groups.setdefault((typ[x], part[x]), []).append(x)
    p = [None] * N
    for (d, q), L in groups.items():
        if d < q:
            M = groups.get((q, d), [])
            assert len(M) == len(L), ("pair row violated", d, q, len(L), len(M))
            M = M[:]; rng.shuffle(M)
            for a, b in zip(L, M):
                p[a] = b; p[b] = a
    assert all(v is not None for v in p)
    # merge components by swaps of same-slot edges
    def comps():
        par = list(range(N))
        def f(a):
            while par[a] != a:
                par[a] = par[par[a]]; a = par[a]
            return a
        for x in range(N):
            for e in (p[x], sigma[x]):
                par[f(x)] = f(e)
        return [f(x) for x in range(N)]
    while True:
        cid = comps()
        if len(set(cid)) == 1:
            break
        done = False
        for (d, q), L in groups.items():
            if d >= q:
                continue
            seen = {}
            for a in L:
                if cid[a] not in seen:
                    seen[cid[a]] = a
            if len(seen) >= 2:
                a1, a2 = list(seen.values())[:2]
                b1, b2 = p[a1], p[a2]
                p[a1] = b2; p[b2] = a1; p[a2] = b1; p[b1] = a2
                done = True
                break
        if not done:
            break
    nxt = [None] * N
    for x in range(N):
        nxt[p[x]] = sigma[x]        # nxt o p = sigma
    for x in range(N):
        assert nxt[x] in [None] or True
    return typ, p, nxt, sigma


def primitive_root(seq):
    L = len(seq)
    for d in range(1, L + 1):
        if L % d == 0 and seq[:d] * (L // d) == seq:
            return seq[:d], L // d
    return seq, 1


def canon(seq):
    L = len(seq)
    return min(tuple(seq[k:] + seq[:k]) for k in range(L))


def circles_of(nxt):
    N = len(nxt); seen = [False] * N; out = []
    for x in range(N):
        if not seen[x]:
            o = []; e = x
            while not seen[e]:
                seen[e] = True; o.append(e); e = nxt[e]
            out.append(o)
    return out


def circle_info(TY, typ, o):
    T0 = TY.T[typ[o[0]]]
    if T0[0] == "-":
        letters = [TY.T[typ[x]][1] for x in o]
        root, k = primitive_root(letters)
        return "-", canon(root), k
    blocks = [TY.T[typ[x]][2] for x in o if TY.T[typ[x]][0] == "L"]
    rev = blocks[::-1]
    root, k = primitive_root(rev)
    return "+", canon(root), k


def lift(TY, typ, p, nxt, K, mono):
    """Z/K cover with prescribed circle monodromies mono[circle]; the monodromies must sum to 0
    mod K on every component of X (= component of the circle-adjacency graph).  The whole cover
    (all K sheets, possibly disconnected) is returned: circle C lifts to gcd(mono C, K) circles."""
    N = len(p)
    circ = circles_of(nxt)
    cid = [0] * N
    for i, o in enumerate(circ):
        for x in o:
            cid[x] = i
    nc = len(circ)
    adj = [[] for _ in range(nc)]
    for x in range(N):
        if x < p[x] and cid[x] != cid[p[x]]:
            adj[cid[x]].append((cid[p[x]], x))
            adj[cid[p[x]]].append((cid[x], x))
    g = [0] * N
    need = {i: mono[i] % K for i in range(nc)}
    parent = {}
    for root in range(nc):
        if root in parent:
            continue
        parent[root] = None; order = [root]
        for u in order:
            for (w, x) in adj[u]:
                if w not in parent:
                    parent[w] = (u, x); order.append(w)
        for w in reversed(order[1:]):
            u, x = parent[w]
            # dart x contributes +g_x to circle cid[x], dart p[x] contributes -g_x to cid[p[x]]
            if cid[x] == w:
                g[x] = need[w]; g[p[x]] = -need[w]
            else:
                g[p[x]] = need[w]; g[x] = -need[w]
            need[u] = (need[u] + need[w]) % K
            need[w] = 0
        assert need[root] % K == 0, "monodromies do not sum to 0 on a component"
    for i, o in enumerate(circ):
        assert sum(g[x] for x in o) % K == mono[i] % K
    # cover darts (x, i): p~(x,i) = (p x, i + g_x), nxt~(x,i) = (nxt x, i + g_x), sigma~(x,i) = (sigma x, i)
    idx = lambda x, i: x * K + (i % K)
    P = [0] * (N * K); NX = [0] * (N * K)
    for x in range(N):
        for i in range(K):
            P[idx(x, i)] = idx(p[x], i + g[x])
            NX[idx(x, i)] = idx(nxt[x], i + g[x])
    typ2 = [typ[a // K] for a in range(N * K)]
    return typ2, P, NX


def x_components(p, nxt):
    N = len(p); par = list(range(N))
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for x in range(N):
        for e in (p[x], nxt[p[x]]):
            par[f(x)] = f(e)
    return [f(x) for x in range(N)]


def cover_monodromies(info, comp_of_circle, rng, tmax=40, samples=4000):
    """common K and units u_C with sum_C eps_C k_C u_C = 0 mod K on each X-component,
    gcd(k_C u_C, K) = k_C (so each lift of C has K periods)."""
    L = 1
    for kd, key, k in info:
        L = L * k // gcd(L, k)
    comps = sorted(set(comp_of_circle))
    for t in range(1, tmax + 1):
        K = L * t
        mono = [None] * len(info)
        ok = True
        for cpt in comps:
            cs = [i for i in range(len(info)) if comp_of_circle[i] == cpt]
            base = [(1 if info[i][0] == "-" else -1) * info[i][2] for i in cs]
            if sum(base) % K == 0:
                for i, v in zip(cs, base):
                    mono[i] = v
                continue
            found = None
            for _ in range(samples):
                us = [rng.choice([u for u in range(1, K // info[i][2] + 1) if gcd(u, K // info[i][2]) == 1])
                      for i in cs]
                if sum(b * u for b, u in zip(base, us)) % K == 0:
                    found = us; break
            if found is None:
                ok = False; break
            for i, v, u in zip(cs, base, found):
                mono[i] = v * u
        if ok:
            return K, mono
    return None, None


def matched_certificate(TY, typ, p, nxt):
    circ = circles_of(nxt)
    minus, plus = {}, {}
    for o in circ:
        kind, key, k = circle_info(TY, typ, o)
        (minus if kind == "-" else plus).setdefault(key, []).append(o)
    assert {k: len(v) for k, v in minus.items()} == {k: len(v) for k, v in plus.items()}, \
        ("unmatched", {k: len(v) for k, v in minus.items()}, {k: len(v) for k, v in plus.items()})
    order = []; words = []
    for key in sorted(minus):
        for om, op in zip(minus[key], plus[key]):
            w = [TY.T[typ[x]][1] for x in om]
            L = len(w)
            bstarts = [i for i, x in enumerate(op)
                       if (TY.T[typ[x]][0] == "+" and TY.T[typ[x]][2] == 0)
                       or (TY.T[typ[x]][0] == "L" and len(TY.R[TY.T[typ[x]][2]]) == 1)]
            blk = []
            for i in bstarts:
                t = TY.T[typ[op[i]]]
                blk.append(t[1] if t[0] == "+" else t[2])
            assert len(blk) == L
            target = w[::-1]
            j0 = next(j for j in range(L) if blk[j:] + blk[:j] == target)
            s = bstarts[j0]
            order.extend(om)
            order.extend(op[s:] + op[:s])
            words.append("".join(w))
    ren = {a: i for i, a in enumerate(order)}
    N = len(order)
    pairing = [ren[p[a]] for a in order]
    labels = [TY.label[typ[a]] for a in order]
    return words, labels, pairing


def main():
    args = sys.argv[1:]
    phi0 = json.loads(args[0]); m = int(args[1]); out = args[2]
    perm = "--perm" in args
    seed = int(args[args.index("--seed") + 1]) if "--seed" in args else 1
    cmax = int(args[args.index("--cmax") + 1]) if "--cmax" in args else 60
    rng = random.Random(seed)
    t0 = time.time()
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    TY = LA.Types(phi, g)
    polys = LA.polygons(TY, g, max(2, 2 * min(gp, gn)))
    print("polygons", len(polys), "t", round(time.time() - t0, 1), flush=True)
    tries = int(args[args.index("--tries") + 1]) if "--tries" in args else 6
    base = None
    for t in range(tries):
        K = None if t == 0 else base * (1 + (t - 1) // 3)
        y, cnt, res = int_solution(TY, polys, perm, cmax=cmax, K=K, rng=rng)
        if y is None:
            print("MILP: no integer solution", K, res.status, res.message, flush=True)
            if t == 0:
                sys.exit(2)
            continue
        if base is None:
            base = sum(cnt.values())
        chi = sum(n * (1 - len(polys[j]) / 2) for j, n in y.items())
        print("try", t, "MILP sum c", sum(cnt.values()), "chi", chi, "turns", cnt, "vertices", sum(y.values()),
              "t", round(time.time() - t0, 1), flush=True)
        succ = {}
        for (a_, b_) in cnt:
            succ.setdefault(a_, set()).add(b_)
        print("permutation support:", all(len(v) == 1 for v in succ.values()), flush=True)
        typ, p, nxt, sigma = positions_fatgraph(TY, polys, y, rng)
        N = len(typ)
        for x in range(N):
            assert typ[nxt[x]] in TY.succ[typ[x]], "type succession fails"
            assert TY.label[typ[p[x]]] == inv(TY.label[typ[x]])
            assert nxt[p[x]] == sigma[x]
        circ = circles_of(nxt)
        info = [circle_info(TY, typ, o) for o in circ]
        cx = x_components(p, nxt)
        print("base fatgraph darts", N, "X components", len(set(cx)),
              "circles", [(kd, "".join(key), k) for kd, key, k in info], flush=True)
        tot = {}
        for kd, key, k in info:
            tot.setdefault(key, [0, 0])[kd == "+"] += k
        print("period totals per root (minus, plus):", {"".join(k): v for k, v in tot.items()}, flush=True)
        if any(a_ != b_ for a_, b_ in tot.values()):
            print("period totals unbalanced (support not a permutation?)", flush=True)
            continue
        Kc, mono = cover_monodromies(info, [cx[o[0]] for o in circ], rng)
        if Kc is None:
            print("no cyclic cover found", flush=True)
            continue
        break
    else:
        print("giving up", flush=True); sys.exit(4)
    typ2, p2, nxt2 = lift(TY, typ, p, nxt, Kc, mono)
    print("cover degree", Kc, "monodromies", mono, "cover darts", len(typ2), flush=True)
    words, labels, pairing = matched_certificate(TY, typ2, p2, nxt2)
    # restrict to one component of S*_f(X) with chi < 0
    Nw = len(labels)
    starts = []; pos = 0
    circles = []
    for w in words:
        circles.append((pos, len(w))); pos += len(w)
        plen = sum(len(TY.R[x]) for x in w)
        circles.append((pos, plen)); pos += plen
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
        dset = set(ds)
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
    print("S* components", len(groups), "chosen chi", best[0], "darts", len(best[1]), flush=True)
    keep = set(best[1])
    new_words = []; order = []
    for i, w in enumerate(words):
        s0, L = circles[2 * i]
        if s0 in keep:
            new_words.append(w)
            order.extend(range(s0, s0 + L))
            s1, L1 = circles[2 * i + 1]
            order.extend(range(s1, s1 + L1))
    ren = {a_: i for i, a_ in enumerate(order)}
    pairing = [ren[pairing[a_]] for a_ in order]
    labels = [labels[a_] for a_ in order]
    words = new_words
    cert = {"phi0": phi0, "power": m, "phi": phi, "minus_words": words, "labels": labels,
            "pairing": pairing, "construction": "lift_lp.py seed %d perm %s cover %d" % (seed, perm, Kc),
            "milp_turns": {"%s%s" % t: v for t, v in cnt.items()},
            "milp_polygons": [[n, [[TY.T[d], TY.T[q]] for d, q in polys[j]]] for j, n in sorted(y.items())]}
    json.dump(cert, open(out, "w"))
    here = os.path.dirname(os.path.abspath(__file__))
    print("minus words", len(words), "lengths", sorted(len(w) for w in words), flush=True)
    rc = 5
    for chk in ("verify_surface.py", "verify_surface_multi.py"):
        r = subprocess.run(["python3", os.path.join(here, chk), out], capture_output=True, text=True)
        print(chk, r.stdout.strip()[:700], r.stderr.strip()[-300:], flush=True)
        if r.returncode == 0:
            rc = 0
    sys.exit(rc)


if __name__ == "__main__":
    main()
