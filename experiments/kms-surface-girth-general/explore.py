#!/usr/bin/env python3
"""Lane hl-surface-girth-general (2026-09-14): exact F_p labelling experiments for KMS girth surfaces.

Vertex words are evaluated with the normal-form laws of U3(p) and U4(p) (Step 0(a) of
kms-girth-surfaces-give-surface-subgroups-proof), at three levels:
  ab    both exponent sums vanish
  heis  ab and the area coordinate mu vanishes
  full  heis and, for U4, the cubic coordinate nu vanishes
A vertex can also be deactivated (its word unconstrained).  Girth surfaces come from kms_girth_search.surfaces,
so surface indices agree with the landed searches.

usage:
  explore.py dump  FAMILY T P            write surf-<FAMILY>-t<T>.json
  explore.py calib FAMILY T P i,j,...    full labelling counts
  explore.py cores FAMILY T P i,j,...    levels, single-vertex removals and relaxations, greedy minimal core
  explore.py feas  FAMILY T P [maxnodes] full feasibility of every girth surface
"""
import sys, json, time, os
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault("KMS_LABELS", "-2,-1,1,2")
import kms_girth_search as K

PAIR = K.PAIR


def law(kind, letters, p, level):
    if kind[0] == "U3":
        xk = letters[0][0]; beta = alpha = mu = 0
        for k, e in letters:
            if k == xk: alpha += e
            else: mu += alpha * e; beta += e
        ok = beta % p == 0 and alpha % p == 0
        return ok if level == "ab" else ok and mu % p == 0
    xk = kind[1]; beta = gamma = mu = nu = 0
    for k, e in letters:
        if k == xk: gamma += e
        else: nu += gamma * e * (e - 1) // 2 + e * mu; mu += e * gamma; beta += e
    ok = beta % p == 0 and gamma % p == 0
    if level == "ab": return ok
    ok = ok and mu % p == 0
    if level == "heis": return ok
    return ok and nu % p == 0


WCACHE = {}
def closed_words(i, m, kind, p, level):
    key = (i, m, kind, p, level)
    if key in WCACHE: return WCACHE[key]
    types = [PAIR[i][q & 1] for q in range(2 * m)]
    halves = []
    for t in product(range(1, p), repeat=m - 1):
        last = (-sum(t)) % p
        if last: halves.append(t + (last,))
    out = []
    for xe in halves:
        for ye in halves:
            w = [0] * (2 * m); w[0::2] = xe; w[1::2] = ye
            if law(kind, list(zip(types, w)), p, level): out.append(tuple(w))
    WCACHE[key] = out
    return out


def masks(words, L, p):
    ms = [[0] * p for _ in range(L)]
    for n, w in enumerate(words):
        bit = 1 << n
        for q, e in enumerate(w): ms[q][e] |= bit
    return ms, (1 << len(words)) - 1


def structure(r, T, M):
    eid, edges = {}, []
    for k in range(3):
        for t in range(T):
            if t < r[k][t]: eid[(k, t)] = len(edges); edges.append((k, t, r[k][t]))
    verts = []
    for i in range(3):
        j, k = PAIR[i]; seen = [False] * T
        for t0 in range(T):
            if seen[t0]: continue
            occ, t, cur, q = [], t0, j, 0
            while True:
                seen[t] = True; s = r[cur][t]
                occ.append((eid[(cur, min(t, s))], 1 if t < s else -1, q))
                t = s; cur = k if cur == j else j; q += 1
                if t == t0 and cur == j: break
            assert len(occ) == 2 * M[i]
            verts.append((i, occ))
    return edges, verts


class Cap(Exception):
    pass


def solve(p, nE, verts, active, vm, vf, limit, maxnodes):
    occ_of = [[] for _ in range(nE)]
    for v, (i, occ) in enumerate(verts):
        if active[v]:
            for (e, sg, q) in occ: occ_of[e].append((v, sg, q))
    dom = list(vf); assign = [0] * nE; st = {"n": 0, "nodes": 0, "first": []}

    def vals_of(e):
        out = []
        for x in range(1, p):
            ds = []
            for (v, sg, q) in occ_of[e]:
                a = dom[v] & vm[v][q][x if sg > 0 else p - x]
                if not a: break
                ds.append((v, a))
            else:
                out.append((x, ds))
        return out

    def dfs(depth):
        st["nodes"] += 1
        if st["nodes"] > maxnodes: raise Cap()
        if depth == nE:
            st["n"] += 1
            if len(st["first"]) < 2: st["first"].append(list(assign))
            return
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
            if st["n"] >= limit: break
        assign[best] = 0

    try:
        dfs(0); status = "done"
    except Cap:
        status = "cap"
    return st["n"], st["nodes"], status, st["first"]


def run(fam, T, p, r, levels, active, limit, maxnodes):
    M, kinds = K.FAMILIES[fam]
    edges, verts = structure(r, T, M)
    vm, vf = [], []
    for v, (i, occ) in enumerate(verts):
        W = closed_words(i, M[i], kinds[i], p, levels[v])
        ms, full = masks(W, 2 * M[i], p); vm.append(ms); vf.append(full)
    return solve(p, len(edges), verts, active, vm, vf, limit, maxnodes), edges, verts


def surfaces_of(fam, T):
    M, _ = K.FAMILIES[fam]
    return K.surfaces(T, M)


def main():
    cmd, fam, T, p = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    M, kinds = K.FAMILIES[fam]
    t0 = time.time()
    S = surfaces_of(fam, T)
    print("family", fam, "T", T, "p", p, "girth surfaces", len(S), "sec", round(time.time() - t0, 1), flush=True)
    if cmd == "dump":
        json.dump({"family": fam, "T": T, "M": list(M), "surfaces": S, "orientable": [K.orientable(r, T) for r in S]},
                  open("surf-%s-t%d.json" % (fam, T), "w"))
        return
    if cmd == "feas":
        cap = int(sys.argv[5]) if len(sys.argv) > 5 else 3 * 10 ** 7
        for n, r in enumerate(S):
            edges, verts = structure(r, T, M)
            lv = ["full"] * len(verts); act = [True] * len(verts)
            (cnt, nodes, status, first), _, _ = run(fam, T, p, r, lv, act, 1, cap)
            print("surface", n, "orientable", K.orientable(r, T), "feasible", cnt > 0, "status", status, "nodes", nodes,
                  "first", first[:1], flush=True)
        return
    idxs = [int(x) for x in sys.argv[5].split(",")]
    for n in idxs:
        r = S[n]; edges, verts = structure(r, T, M); nv = len(verts)
        full = ["full"] * nv; allact = [True] * nv
        if cmd == "calib":
            (cnt, nodes, status, first), _, _ = run(fam, T, p, r, full, allact, 10 ** 9, 10 ** 9)
            print("calib surface", n, "orientable", K.orientable(r, T), "count", cnt, "nodes", nodes, "status", status,
                  "sec", round(time.time() - t0, 1), flush=True)
            continue
        print("== surface", n, "orientable", K.orientable(r, T), "edges", len(edges), flush=True)
        for v, (i, occ) in enumerate(verts):
            print("  vertex", v, "type", i, "occ", [(e, sg) for (e, sg, q) in occ])
        print("  edges", edges)
        def feas(levels, active, cap=5 * 10 ** 7):
            (cnt, nodes, status, first), _, _ = run(fam, T, p, r, levels, active, 1, cap)
            return ("SAT" if cnt else ("UNSAT" if status == "done" else "CAP")), nodes, first[:1]
        print("  all full", feas(full, allact), flush=True)
        print("  all heis", feas(["heis"] * nv, allact), flush=True)
        print("  all ab", feas(["ab"] * nv, allact), flush=True)
        for v in range(nv):
            act = list(allact); act[v] = False
            print("  drop vertex", v, "type", verts[v][0], feas(full, act), flush=True)
        for v in range(nv):
            if kinds[verts[v][0]][0] == "U4":
                lv = list(full); lv[v] = "heis"
                print("  relax vertex", v, "type", verts[v][0], "to heis", feas(lv, allact), flush=True)
        act = list(allact)
        for v in range(nv):
            act[v] = False
            res = feas(full, act)
            if res[0] != "UNSAT": act[v] = True
        core = [v for v in range(nv) if act[v]]
        print("  greedy minimal core (vertices)", core, "types", [verts[v][0] for v in core], flush=True)
        for v in core:
            if kinds[verts[v][0]][0] == "U4":
                lv = list(full); lv[v] = "heis"
                print("  core relax vertex", v, "to heis", feas(lv, act), flush=True)
    print("done sec", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
