#!/usr/bin/env python3
"""Girth surfaces for GHB_2(7) (lane ideas-growth-hyperbolic, 2026-09-14).

A girth surface with T chambers: fixed-point-free involutions r0, r1, r2 on {0..T-1} such that
<r1,r2>, <r0,r2>, <r0,r1> act freely with orbits of size 6, 8, 8 (the vertices of types 0, 1, 2),
and an exponent x_e in 1..6 on every edge.  Crossing a type-k edge from chamber t to s = r_k(t)
multiplies by g_k^(x_e) if t < s and by g_k^(-x_e) otherwise (g_0 = c, g_1 = a, g_2 = b).  The word
around each vertex must be 1 in its vertex group X_0 = <a,b>, X_1 = <c,b>, X_2 = <c,a>, computed
in SL_4(F_7) through psi, which is injective on the vertex groups (cckw-ghb2-kms-group-structure,
item 5).  Every solution gives a genus >= 2 quasiconvex surface subgroup (lane artifact, Theorem A).

usage: calib | surfaces T OUT.json | solve SURF.json OUT.json [limit] | planted SURF.json [seed]
"""
import sys, time, json, random

P = 7
def mul(A, B):
    return tuple(sum(A[4 * r + k] * B[4 * k + c] for k in range(4)) % P for r in range(4) for c in range(4))
def E(i, j, s=1):
    M_ = [0] * 16; M_[4 * i + j] = s % P; return M_
def add(*Ms):
    return tuple(sum(M_[i] for M_ in Ms) % P for i in range(16))
I4 = tuple(1 if r == c else 0 for r in range(4) for c in range(4))
A = add(I4, E(0, 3), E(1, 2)); B = add(I4, E(1, 0), E(2, 3, -1)); C = add(I4, E(3, 1))
GEN = {0: C, 1: A, 2: B}                     # generator carried by edges of type k
PAIR = {0: (1, 2), 1: (0, 2), 2: (0, 1)}     # crossing types around a vertex of type i
M = {0: 3, 1: 4, 2: 4}                       # half-girth type (3,4,4)

def powers(g):
    out = [I4]
    for _ in range(6): out.append(mul(out[-1], g))
    assert mul(out[-1], g) == I4 and all(x != I4 for x in out[1:])
    return out

def vertex_group(i):
    j, k = PAIR[i]; pj, pk = powers(GEN[j]), powers(GEN[k])
    elems = [I4]; idx = {I4: 0}; q = 0
    while q < len(elems):
        g = elems[q]; q += 1
        for h in (GEN[j], GEN[k]):
            x = mul(g, h)
            if x not in idx: idx[x] = len(elems); elems.append(x)
    Rj = [[idx[mul(g, pj[e])] for e in range(7)] for g in elems]
    Rk = [[idx[mul(g, pk[e])] for e in range(7)] for g in elems]
    return len(elems), Rj, Rk

G = {i: vertex_group(i) for i in range(3)}

def words_by_product(i, L, keep):
    """alternating words (exponents 1..6, first letter of type PAIR[i][0]) of length L, bucketed by
    their product in X_i; only products in keep are stored (keep=None stores all)."""
    tabs = (G[i][1], G[i][2]); out = {}
    def rec(g, w, pos):
        if pos == L:
            if keep is None or g in keep: out.setdefault(g, []).append(tuple(w))
            return
        R = tabs[pos & 1]
        for e in range(1, 7):
            w.append(e); rec(R[g][e], w, pos + 1); w.pop()
    rec(0, [], 0)
    return out

def masks_for(words, L):
    ms = [[0] * 7 for _ in range(L)]
    for n, w in enumerate(words):
        bit = 1 << n
        for p, e in enumerate(w): ms[p][e] |= bit
    return ms, (1 << len(words)) - 1

def surfaces(T):
    r = [[-1] * T for _ in range(3)]; nch = [1]; found = []; nodes = [0]
    def path_ok(t, k):
        for j in range(3):
            if j == k: continue
            m2 = 2 * M[3 - j - k]; s, steps, cur, closed = t, 0, k, False
            while True:
                nx = r[cur][s]
                if nx < 0: break
                steps += 1; s = nx; cur = j if cur == k else k
                if s == t: closed = True; break
                if steps >= m2: return False
            if closed:
                if steps != m2: return False
                continue
            s, back, cur = t, 0, j
            while True:
                nx = r[cur][s]
                if nx < 0: break
                back += 1; s = nx; cur = k if cur == j else j
            if steps + back >= m2: return False
        return True
    def relabel(root):
        lab = {root: 0}; order = [root]; q = 0
        while q < len(order):
            u = order[q]; q += 1
            for kk in range(3):
                v = r[kk][u]
                if v not in lab: lab[v] = len(order); order.append(v)
        return tuple(lab[r[kk][u]] for u in order for kk in range(3))
    def record():
        cur = relabel(0)
        assert cur == tuple(r[kk][u] for u in range(T) for kk in range(3))
        if all(relabel(root) >= cur for root in range(1, T)):
            found.append([list(x) for x in r])
    def rec(t, k):
        while t < nch[0] and r[k][t] >= 0:
            k += 1
            if k == 3: k = 0; t += 1
        if t == nch[0]:
            if nch[0] == T: record()
            return
        nodes[0] += 1
        cands = [s for s in range(t + 1, nch[0]) if r[k][s] < 0]
        if nch[0] < T: cands.append(nch[0])
        for s in cands:
            new = (s == nch[0])
            if new: nch[0] += 1
            r[k][t] = s; r[k][s] = t
            if path_ok(t, k) and path_ok(s, k): rec(t, k)
            r[k][t] = -1; r[k][s] = -1
            if new: nch[0] -= 1
    rec(0, 0)
    return found, nodes[0]

def orientable(r, T):
    col = [-1] * T; col[0] = 0; st = [0]
    while st:
        u = st.pop()
        for k in range(3):
            v = r[k][u]
            if col[v] < 0: col[v] = 1 - col[u]; st.append(v)
            elif col[v] == col[u]: return False
    return True

def structure(r, T):
    eid, edges = {}, []
    for k in range(3):
        for t in range(T):
            if t < r[k][t]: eid[(k, t)] = len(edges); edges.append((k, t, r[k][t]))
    verts = []
    for i in range(3):
        j, k = PAIR[i]; seen = [False] * T
        for t0 in range(T):
            if seen[t0]: continue
            occ, t, cur, p = [], t0, j, 0
            while True:
                seen[t] = True; s = r[cur][t]
                occ.append((eid[(cur, min(t, s))], 1 if t < s else -1, p))
                t = s; cur = k if cur == j else j; p += 1
                if t == t0 and cur == j: break
            assert len(occ) == 2 * M[i]
            verts.append((i, occ))
    return edges, verts

def solve(edges, verts, vmasks, vfull, limit):
    nE = len(edges); occ_of = [[] for _ in range(nE)]
    for v, (i, occ) in enumerate(verts):
        for (e, sg, p) in occ: occ_of[e].append((v, sg, p))
    dom = list(vfull); assign = [0] * nE; sols = []; nodes = [0]
    def vals_of(e):
        (v1, s1, p1), (v2, s2, p2) = occ_of[e]
        m1, m2, d1, d2 = vmasks[v1][p1], vmasks[v2][p2], dom[v1], dom[v2]; out = []
        for x in range(1, 7):
            a1 = d1 & m1[x if s1 > 0 else 7 - x]
            if a1:
                a2 = d2 & m2[x if s2 > 0 else 7 - x]
                if a2: out.append((x, a1, a2))
        return out
    def dfs(depth):
        nodes[0] += 1
        if depth == nE: sols.append(list(assign)); return
        best, bvals = None, None
        for e in range(nE):
            if assign[e]: continue
            vs = vals_of(e)
            if not vs: return
            if best is None or len(vs) < len(bvals):
                best, bvals = e, vs
                if len(vs) == 1: break
        (v1, _, _), (v2, _, _) = occ_of[best]; o1, o2 = dom[v1], dom[v2]
        for (x, a1, a2) in bvals:
            assign[best] = x; dom[v1] = a1; dom[v2] = a2
            dfs(depth + 1)
            if len(sols) >= limit: break
        assign[best] = 0; dom[v1] = o1; dom[v2] = o2
    dfs(0)
    return sols, nodes[0]

def vertex_product(edges, occ, x):
    g = I4
    for (e, sg, p) in occ:
        ex = x[e] if sg > 0 else 7 - x[e]
        for _ in range(ex): g = mul(g, GEN[edges[e][0]])
    return g

def verify(r, T, x):
    edges, verts = structure(r, T)
    return all(1 <= v <= 6 for v in x) and all(vertex_product(edges, occ, x) == I4 for (_, occ) in verts)

if __name__ == "__main__":
    cmd = sys.argv[1]; t0 = time.time()
    if cmd == "calib":
        print("orders", [G[i][0] for i in range(3)])
        for i in range(3):
            counts = {L: len(words_by_product(i, L, {0}).get(0, [])) for L in (2, 4, 6, 8)}
            print("type", i, "closed alternating words by length", counts)
    elif cmd == "surfaces":
        T = int(sys.argv[2]); found, nodes = surfaces(T)
        ori = [orientable(r, T) for r in found]
        print("T", T, "classes", len(found), "orientable", sum(ori), "nodes", nodes, "sec", round(time.time() - t0, 1))
        json.dump({"T": T, "surfaces": found, "orientable": ori}, open(sys.argv[3], "w"))
    elif cmd in ("solve", "planted"):
        D = json.load(open(sys.argv[2])); T = D["T"]
        W = {i: words_by_product(i, 2 * M[i], {0})[0] for i in range(3)}
        MK = {i: masks_for(W[i], 2 * M[i]) for i in range(3)}
        print("closed words", {i: len(W[i]) for i in range(3)})
        if cmd == "solve":
            limit = int(sys.argv[4]) if len(sys.argv) > 4 else 20; res = []
            for n, r in enumerate(D["surfaces"]):
                edges, verts = structure(r, T)
                sols, nodes = solve(edges, verts, [MK[i][0] for i, _ in verts], [MK[i][1] for i, _ in verts], limit)
                ok = all(verify(r, T, s) for s in sols)
                res.append({"n": n, "orientable": D["orientable"][n], "solutions": len(sols), "nodes": nodes, "verified": ok, "first": sols[:3]})
                print("surface", n, "orientable", D["orientable"][n], "solutions", len(sols), "nodes", nodes, "verified", ok, flush=True)
            json.dump(res, open(sys.argv[3], "w"))
            print("total surfaces with solutions", sum(1 for z in res if z["solutions"]), "sec", round(time.time() - t0, 1))
        else:
            random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
            n = next(z for z, o in enumerate(D["orientable"]) if o); r = D["surfaces"][n]
            edges, verts = structure(r, T); x = [random.randint(1, 6) for _ in edges]
            need = {i: set() for i in range(3)}; tgt = []
            for (i, occ) in verts:
                g, tabs = 0, (G[i][1], G[i][2])
                for (e, sg, p) in occ: g = tabs[p & 1][g][x[e] if sg > 0 else 7 - x[e]]
                need[i].add(g); tgt.append(g)
            byp = {i: words_by_product(i, 2 * M[i], need[i]) for i in range(3)}
            vm, vf = [], []
            for v, (i, occ) in enumerate(verts):
                ms, full = masks_for(byp[i][tgt[v]], 2 * M[i]); vm.append(ms); vf.append(full)
            sols, nodes = solve(edges, verts, vm, vf, 10 ** 6)
            print("planted surface", n, "solutions", len(sols), "planted found", x in sols, "nodes", nodes, "sec", round(time.time() - t0, 1))
