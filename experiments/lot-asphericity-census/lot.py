#!/usr/bin/env python3
"""Certified asphericity tests for labelled oriented trees (LOTs).

A LOG on vertices 0..n-1 is a list of edges (i, l, t): initial vertex, label, terminal
vertex.  Relator of (i, l, t): i l t^-1 l^-1, i.e. i l = l t (Harlander--Rosebrock).
Every test is sound for LOT complexes; each cites the pinned source in its docstring.
"""
from fractions import Fraction as Fr
import itertools, heapq

def rel(e):
    i, l, t = e
    return [(i, 1), (l, 1), (t, -1), (l, -1)]

# ---------------------------------------------------------------- reductions
def reduce_lot(n, edges):
    """Howie's moves (Harlander--Rosebrock, arXiv:1212.1943, Sec. 1): compress, boundary
    reduce, interior reduce.  Each is a 3-deformation, so K(G) ~ K(G_red)."""
    V, E = set(range(n)), [tuple(e) for e in edges]
    while True:
        k = next((k for k, (i, l, t) in enumerate(E) if l in (i, t)), None)
        if k is not None:
            i, l, t = E[k]; a, b = l, (t if l == i else i)
            E = [tuple(a if x == b else x for x in e) for j, e in enumerate(E) if j != k]
            V.discard(b); continue
        deg = {v: 0 for v in V}
        for (i, l, t) in E: deg[i] += 1; deg[t] += 1
        labels = {l for (_, l, _) in E}
        hit = None
        for k, (i, l, t) in enumerate(E):
            for a in (i, t):
                if deg[a] == 1 and a not in labels: hit = (k, a); break
            if hit: break
        if hit:
            E = [e for j, e in enumerate(E) if j != hit[0]]; V.discard(hit[1]); continue
        hit = None
        for j, k in itertools.combinations(range(len(E)), 2):
            (i1, l1, t1), (i2, l2, t2) = E[j], E[k]
            if l1 != l2: continue
            if t1 == t2: hit = (k, i1, i2); break
            if i1 == i2: hit = (k, t1, t2); break
        if hit:
            k, a, c = hit
            E = [tuple(a if x == c else x for x in e) for m, e in enumerate(E) if m != k]
            V.discard(c); continue
        break
    idx = {v: r for r, v in enumerate(sorted(V))}
    return len(V), [tuple(idx[x] for x in e) for e in E]

def is_reduced(n, edges):
    return reduce_lot(n, edges)[0] == n

# ---------------------------------------------------------------- cheap tests
def cyclomatic(nv, pairs):
    p = list(range(nv))
    def f(x):
        while p[x] != x: p[x] = p[p[x]]; x = p[x]
        return x
    extra = 0
    for u, v in pairs:
        ru, rv = f(u), f(v)
        if ru == rv: extra += 1
        else: p[ru] = rv
    return extra

def test_IT(n, E):
    """Barreto--Minian arXiv:2308.07447 Cor. 3.1: I(G) or T(G) has at most one cycle =>
    G(G) locally indicable; with H_2(K(G)) = 0 this gives asphericity (Howie).  Tree case:
    Howie 1985 Thm 10.1, Gersten Prop. 4.15 (DR).  Applied to reduced LOTs only."""
    ci = cyclomatic(n, [(l, t) for (i, l, t) in E])
    ct = cyclomatic(n, [(l, i) for (i, l, t) in E])
    return {'I_cyc': ci, 'T_cyc': ct} if min(ci, ct) <= 1 else None

def diameter(n, E):
    adj = {v: [] for v in range(n)}
    for (i, l, t) in E: adj[i].append(t); adj[t].append(i)
    best = 0
    for s in range(n):
        d = {s: 0}; q = [s]
        for u in q:
            for w in adj[u]:
                if w not in d: d[w] = d[u] + 1; q.append(w)
        best = max(best, max(d.values()))
    return best

def test_diam(n, E):
    """Howie 1985 (Trans. AMS 289), via Rosebrock 2007 survey item (2): diameter <= 3."""
    return {'diam': diameter(n, E)} if diameter(n, E) <= 3 else None

def test_inj(n, E):
    """Harlander--Rosebrock, Math. Z. 287 (2017), Thm 1.1: injective LOTs are aspherical."""
    ls = [l for (_, l, _) in E]
    return {'injective': True} if len(set(ls)) == len(ls) else None

def test_cx2(n, E):
    """Rosebrock 2007 survey Thm 4.6: LOTs of complexity 2 are aspherical.  A reduced LOT
    with >= 2 vertices has complexity >= 2, so a deriving pair certifies complexity 2."""
    if n < 2: return None
    for S in itertools.combinations(range(n), 2):
        good = set(S); grow = True
        while grow:
            grow = False
            for (i, l, t) in E:
                if l in good and i in good and t not in good: good.add(t); grow = True
                if l in good and t in good and i not in good: good.add(i); grow = True
        if len(good) == n: return {'S': list(S)}
    return None

# ---------------------------------------------------------------- I-test
def weight_matrix(n, rels, v):
    m = len(rels); M = [[[] for _ in range(m)] for _ in range(n)]
    for j, w in enumerate(rels):
        L = len(w)
        for k, (g, eps) in enumerate(w):
            start = k if eps == 1 else k + 1
            M[g][j].append(sum(e * v[h] for (h, e) in w[start:L]))
    return M

def good_orderings(M, n, m):
    """Barmak--Minian Def. 2.5, greedy (Remark 2.9: valid partial orderings extend)."""
    if n < m: return None
    rowmax = [max((x for col in M[i] for x in col), default=None) for i in range(n)]
    R, used, rows, cols = set(range(m)), set(), [], []
    for _ in range(m):
        pick = None
        for i in range(n):
            if i in used or rowmax[i] is None: continue
            rest = [x for j in R for x in M[i][j]]
            for j in sorted(R):
                if M[i][j] and max(M[i][j]) == rowmax[i] and rest.count(rowmax[i]) == 1:
                    pick = (i, j); break
            if pick: break
        if not pick: return None
        used.add(pick[0]); R.discard(pick[1]); rows.append(pick[0]); cols.append(pick[1])
    return rows, cols

def verify_itest(n, rels, v, rows, cols):
    m = len(rels)
    for w in rels:  # v orthogonal to every q(r_j)
        if sum(e * v[g] for (g, e) in w) != 0: return False
    if sorted(cols) != list(range(m)) or len(set(rows)) != m: return False
    M = weight_matrix(n, rels, v)
    for k in range(m):
        i, j = rows[k], cols[k]
        allrow = [x for col in M[i] for x in col]
        rest = [x for jj in cols[k:] for x in M[i][jj]]
        if not M[i][j] or max(M[i][j]) != max(allrow) or rest.count(max(M[i][j])) != 1:
            return False
    return True

def test_itest(n, E, rels=None, vs=None):
    """Barmak--Minian, Proc. Roy. Soc. Edinburgh A 150 (2020), Thms 2.6/2.8: I-test => DR.
    For a LOT, v must be constant on the tree, so v = (1,...,1) or (-1,...,-1)."""
    rels = rels or [rel(e) for e in E]
    for v in (vs or [[1] * n, [-1] * n]):
        o = good_orderings(weight_matrix(n, rels, v), n, len(rels))
        if o and verify_itest(n, rels, v, *o):
            return {'v': v, 'rows': o[0], 'cols': o[1]}
    return None

# ---------------------------------------------------------------- weight test
def link(n, rels):
    """Whitehead graph (Barmak--Minian Sec. 3): corner k of w gives edge
    (eps_k x_{i_k}, -eps_{k+1} x_{i_{k+1}}).  Vertex code 2g (sign +) or 2g+1 (sign -)."""
    edges, face = [], []
    for j, w in enumerate(rels):
        L = len(w)
        for k in range(L):
            (g1, e1), (g2, e2) = w[k], w[(k + 1) % L]
            edges.append((2 * g1 + (0 if e1 == 1 else 1), 2 * g2 + (0 if -e2 == 1 else 1)))
            face.append(j)
    return edges, face

def min_cycle(nv, edges, w):
    """Minimum weight of a simple cycle (nonnegative weights): min over edges e=(u,v) of
    w_e + dist_{G-e}(u, v).  Returns (weight, edge-index list) or (None, None)."""
    best, arg = None, None
    adj = [[] for _ in range(nv)]
    for k, (u, v) in enumerate(edges):
        adj[u].append((v, k)); adj[v].append((u, k))
    for k, (u, v) in enumerate(edges):
        if u == v: cand, path = w[k], [k]
        else:
            dist, prev, pq = {u: 0}, {}, [(0, u)]
            while pq:
                d, x = heapq.heappop(pq)
                if d != dist.get(x): continue
                for (y, kk) in adj[x]:
                    if kk == k: continue
                    nd = d + w[kk]
                    if y not in dist or nd < dist[y]:
                        dist[y] = nd; prev[y] = (x, kk); heapq.heappush(pq, (nd, y))
            if v not in dist: continue
            cand, path, x = w[k] + dist[v], [k], v
            while x != u: x, kk = prev[x]; path.append(kk)
        if best is None or cand < best: best, arg = cand, path
    return best, arg

def verify_weight(n, rels, wts):
    edges, face = link(n, rels)
    if len(wts) != len(edges) or any(x < 0 for x in wts): return False
    for j, r in enumerate(rels):
        if sum(wts[k] for k in range(len(edges)) if face[k] == j) > len(r) - 2: return False
    mc, _ = min_cycle(2 * n, edges, wts)
    return mc is None or mc >= 2

def test_weight(n, E, rels=None, max_rounds=400):
    """Nonnegative weight test (Gersten 1987; Harlander--Rosebrock Canad. Math. Bull. 64
    (2021) Def. 3.5: faces <= q-2, reduced cycles >= 2 => aspherical).  With nonnegative
    weights every reduced cycle contains a simple cycle, so simple cycles suffice.
    Float LP with cutting planes, then exact rational verification."""
    from scipy.optimize import linprog
    rels = rels or [rel(e) for e in E]
    edges, face = link(n, rels); ne = len(edges)
    A, b = [], []
    for j, r in enumerate(rels):
        A.append([1.0 if face[k] == j else 0.0 for k in range(ne)]); b.append(len(r) - 2)
    for _ in range(max_rounds):
        res = linprog([1.0] * ne, A_ub=A, b_ub=b, bounds=[(0, 2)] * ne, method='highs')
        if res.status != 0: return None
        for den in (1, 2, 3, 4, 6, 12, 60, 840):
            q = [Fr(round(x * den), den) for x in res.x]
            if verify_weight(n, rels, q): return {'weights': [str(x) for x in q]}
        mc, cyc = min_cycle(2 * n, edges, list(res.x))
        if mc is None or mc >= 2 - 1e-9:
            q = [Fr(x).limit_denominator(10 ** 6) for x in res.x]
            return {'weights': [str(x) for x in q]} if verify_weight(n, rels, q) else None
        row = [0.0] * ne
        for k in cyc: row[k] -= 1.0
        A.append(row); b.append(-2.0)
    return None

TESTS = [('diam', test_diam), ('inj', test_inj), ('IT', test_IT), ('cx2', test_cx2),
         ('itest', test_itest), ('weight', test_weight)]

def certify(n, edges):
    """Reduce, then return (reduced LOT, first passing test, certificate) or (red, None, None)."""
    rn, rE = reduce_lot(n, edges)
    if rn <= 1: return (rn, rE), 'trivial', {}
    for name, f in TESTS:
        c = f(rn, rE)
        if c is not None: return (rn, rE), name, c
    return (rn, rE), None, None
