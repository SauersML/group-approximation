#!/usr/bin/env python3
"""Shannon-type (polymatroid) lower bounds for the Rokhlin window functional Phi.

Configuration (k, E, F, psi) over a group G, x iid uniform on (A^k)^G, y_g = psi(x|_{gE}).
Normalise H(x(g)) = k log q = 1. Maximality at the configuration is Phi >= 1, where

    Phi = H(y_1) + H(x(1) | y_F).

The LP minimises Phi over all polymatroids h on the ground set
    { x_g : g in X } u { y_g : g in Y }
subject to
  (I)  x_g independent, h(x_g) = 1;
  (D)  h(y_g u x_{gE}) = h(x_{gE})  (y_g is a function of its window);
  (T)  h(S) = h(gS) whenever S and gS both lie in the ground set (left translation);
and all elemental Shannon inequalities. Every entropy function of a genuine
configuration satisfies these constraints, so LP value < 1 means no Shannon-type
derivation that uses only the variables of this window can prove Phi >= 1.

Groups: words in the free group on a, b (A = a^-1, B = b^-1), or Z^d as tuples.
"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

# ---------------- groups ----------------
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', 'c': 'C', 'C': 'c'}

class Free:
    one = ''
    @staticmethod
    def mul(u, v):
        s = list(u)
        for ch in v:
            if s and s[-1] == INV[ch]:
                s.pop()
            else:
                s.append(ch)
        return ''.join(s)
    @staticmethod
    def inv(u):
        return ''.join(INV[ch] for ch in reversed(u))
    @staticmethod
    def show(u):
        return u if u else '1'

class Zd:
    def __init__(self, d):
        self.one = (0,) * d
    def mul(self, u, v):
        return tuple(p + q for p, q in zip(u, v))
    def inv(self, u):
        return tuple(-p for p in u)
    def show(self, u):
        return str(u)

# ---------------- LP ----------------
class UF:
    def __init__(self, n):
        self.p = list(range(n))
    def find(self, i):
        while self.p[i] != i:
            self.p[i] = self.p[self.p[i]]
            i = self.p[i]
        return i
    def union(self, i, j):
        i, j = self.find(i), self.find(j)
        if i != j:
            self.p[max(i, j)] = min(i, j)

def build(G, E, F, X=None, Y=None):
    """Return LP data. X, Y default to FE u {1} and F."""
    if Y is None:
        Y = list(dict.fromkeys(F))
    if X is None:
        X = [G.one]
        for f in Y:
            for e in E:
                X.append(G.mul(f, e))
    X = list(dict.fromkeys(X))
    for g in Y:
        for e in E:
            assert G.mul(g, e) in X, 'window of y_%s not in X' % G.show(g)
    items = [('x', g) for g in X] + [('y', g) for g in Y]
    idx = {it: i for i, it in enumerate(items)}
    n = len(items)
    N = 1 << n
    # translations: all p q^-1 with p, q sites
    sites = list(dict.fromkeys(X + Y))
    trans = set()
    for p in sites:
        for q in sites:
            trans.add(G.mul(p, G.inv(q)))
    trans.discard(G.one)
    allm = np.arange(N, dtype=np.int64)
    src_e, dst_e = [], []
    for t in trans:
        im = [idx.get((kind, G.mul(t, g)), -1) for (kind, g) in items]
        img = np.zeros(N, dtype=np.int64)
        bad = np.zeros(N, dtype=bool)
        for i in range(n):
            has = (allm >> i) & 1 == 1
            if im[i] < 0:
                bad |= has
            else:
                img |= np.where(has, 1 << im[i], 0)
        ok = ~bad
        src_e.append(allm[ok]); dst_e.append(img[ok])
    from scipy.sparse.csgraph import connected_components
    if src_e:
        s = np.concatenate(src_e); t_ = np.concatenate(dst_e)
    else:
        s = t_ = np.zeros(0, dtype=np.int64)
    gph = coo_matrix((np.ones(len(s)), (s, t_)), shape=(N, N))
    nv, col = connected_components(gph, directed=True, connection='weak')
    col = col.astype(np.int64)
    return dict(G=G, E=E, F=list(dict.fromkeys(F)), X=X, Y=Y, items=items, idx=idx, n=n, col=col, nv=nv)

def mask(d, its):
    m = 0
    for it in its:
        m |= 1 << d['idx'][it]
    return m

def constraints(d):
    n, col, G, E = d['n'], d['col'], d['G'], d['E']
    N = 1 << n
    rows, cols, vals = [], [], []
    r = 0
    ineq_desc = []
    full = N - 1
    # monotonicity at top: h(full) - h(full - i) >= 0  ->  -h(full)+h(full-i) <= 0
    for i in range(n):
        for c, v in ((col[full], -1.0), (col[full ^ (1 << i)], 1.0)):
            rows.append(r); cols.append(c); vals.append(v)
        ineq_desc.append(('mono', i)); r += 1
    for i in range(n):
        for j in range(i + 1, n):
            rest = [k for k in range(n) if k != i and k != j]
            for sub in range(1 << len(rest)):
                K = 0
                for t, k in enumerate(rest):
                    if sub >> t & 1:
                        K |= 1 << k
                # h(ijK) + h(K) - h(iK) - h(jK) <= 0
                acc = {}
                for m, v in ((K | 1 << i | 1 << j, 1.0), (K, 1.0), (K | 1 << i, -1.0), (K | 1 << j, -1.0)):
                    c = col[m]
                    acc[c] = acc.get(c, 0.0) + v
                nz = [(c, v) for c, v in acc.items() if v != 0 and not (c == col[0])]
                if not nz:
                    continue
                for c, v in nz:
                    rows.append(r); cols.append(c); vals.append(v)
                ineq_desc.append(('sub', i, j, K)); r += 1
    nv = d['nv']
    A_ub = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
    # drop duplicate rows (translation merging makes many elemental inequalities coincide)
    A_ub.sort_indices()
    keys = {}
    keep = []
    for i in range(A_ub.shape[0]):
        s, e = A_ub.indptr[i], A_ub.indptr[i + 1]
        k = (A_ub.indices[s:e].tobytes(), A_ub.data[s:e].tobytes())
        if k not in keys:
            keys[k] = i
            keep.append(i)
    A_ub = A_ub[keep]
    ineq_desc = [ineq_desc[i] for i in keep]
    r = len(keep)
    b_ub = np.zeros(r)
    # equalities
    er, ec, ev, eb = [], [], [], []
    q = 0
    def eq(terms, rhs):
        nonlocal q
        acc = {}
        for m, v in terms:
            c = col[m]
            acc[c] = acc.get(c, 0.0) + v
        for c, v in acc.items():
            if v != 0:
                er.append(q); ec.append(c); ev.append(v)
        eb.append(rhs); q += 1
    eq([(0, 1.0)], 0.0)
    X = d['X']
    for g in X:
        eq([(mask(d, [('x', g)]), 1.0)], 1.0)
    eq([(mask(d, [('x', g) for g in X]), 1.0)], float(len(X)))
    for g in d['Y']:
        w = [('x', G.mul(g, e)) for e in E]
        eq([(mask(d, w + [('y', g)]), 1.0), (mask(d, w), -1.0)], 0.0)
    A_eq = coo_matrix((ev, (er, ec)), shape=(q, nv)).tocsr()
    b_eq = np.array(eb)
    return A_ub, b_ub, A_eq, b_eq, ineq_desc

def objective(d):
    G, F = d['G'], d['F']
    c = np.zeros(d['nv'])
    yF = [('y', f) for f in F]
    for m, v in ((mask(d, [('y', F[0])]), 1.0), (mask(d, [('x', G.one)] + yF), 1.0), (mask(d, yF), -1.0)):
        c[d['col'][m]] += v
    return c

def solve(d):
    A_ub, b_ub, A_eq, b_eq, desc = constraints(d)
    c = objective(d)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs-ipm')
    return res, (A_ub, b_ub, A_eq, b_eq, desc, c)

def show(G, S):
    return '{' + ','.join(G.show(s) for s in S) + '}'

if __name__ == '__main__':
    G = Free
    E = ['', 'a', 'b']
    F = ['', 'A', 'B']
    d = build(G, E, F)
    res, _ = solve(d)
    print('sunflower', d['n'], d['nv'], res.status, res.fun)
