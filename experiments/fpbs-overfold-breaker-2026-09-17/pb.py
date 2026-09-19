"""Pullback model of the depth-j promotion problem, with seeds reduced to
one representative per (pair-tree type, point of Q).

Conventions follow experiments/fpbs-depth-overfolding-2026-09-17/foldlib.py:
Q = {0..n-1}, right action p.a = PA[p], p.b = PB[p]; phi(a)=a,
phi(b)=b a b^-1 b^-1, t_j = phi^j(b), L_j = <a, t_j>.

Gamma_{j+1}(Q) = Q x_R C_{j+1}   (pullback form, proved in the (O) node),
m = id x iota : Gamma_{j+1}(Q) -> Gamma_j(Q) = Q x_R C_j.
A seed is (q; c, c') with c != c' in V(C_{j+1}); it is lawful iff
iota c = iota c'.  Seeds (q; c, c') and (q.w; c.w, c'.w) (w readable at both
c and c') have the same fold closure, so one root pair per component of the
off-diagonal pair graph C_{j+1} x_R C_{j+1}, times every q, lists every
closure a single seed can produce.
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import Fold, A, t  # noqa: E402

KEYS = [('a', 1), ('a', -1), ('b', 1), ('b', -1)]
KI = {k: i for i, k in enumerate(KEYS)}


def core(j):
    """Stallings core of L_j = <a, t_j>: returns (nb, word) with nb[v][i]
    the neighbour along KEYS[i] (or -1) and word[v] a path from the base 0."""
    F = Fold()
    F.new()
    for w in (A, t(j)):
        F.add_path(0, w, 0)
    roots = F.roots()
    idx = {F.find(0): 0}
    for r in roots:
        if r not in idx:
            idx[r] = len(idx)
    V = len(idx)
    nb = [[-1] * 4 for _ in range(V)]
    for r in roots:
        for k, v in F.adj[r].items():
            nb[idx[r]][KI[k]] = idx[F.find(v)]
    word = [None] * V
    word[0] = []
    st = [0]
    while st:
        v = st.pop()
        for i in range(4):
            u = nb[v][i]
            if u >= 0 and word[u] is None:
                word[u] = word[v] + [i]
                st.append(u)
    return nb, word


def iota(Cs, Cb):
    """Immersion C_{j+1} -> C_j by reading base words."""
    nbs, words = Cs
    nbb, _ = Cb
    out = []
    for v in range(len(nbs)):
        x = 0
        for i in words[v]:
            x = nbb[x][i]
            assert x >= 0
        out.append(x)
    return out


def pair_types(C, io):
    """Components of the off-diagonal pair graph of C, unordered.  Returns
    list of (root pair, lawful flag, size)."""
    nb, _ = C
    V = len(nb)
    seen = {}
    types = []
    for c in range(V):
        for d in range(c + 1, V):
            if (c, d) in seen:
                continue
            comp = [(c, d)]
            seen[(c, d)] = len(types)
            st = [(c, d)]
            while st:
                x, y = st.pop()
                for i in range(4):
                    u, v = nb[x][i], nb[y][i]
                    if u >= 0 and v >= 0:
                        key = (u, v) if u < v else (v, u)
                        assert u != v
                        if key not in seen:
                            seen[key] = len(types)
                            comp.append(key)
                            st.append(key)
            types.append(((c, d), io[c] == io[d], len(comp)))
    return types


class Level:
    def __init__(self, PA, PB, j, C=None):
        n = len(PA)
        self.n = n
        IA = [0] * n
        IB = [0] * n
        for i in range(n):
            IA[PA[i]] = i
            IB[PB[i]] = i
        act = [PA, IA, PB, IB]
        if C is None:
            C = model(j)
        Cs, Cb, io, types = C
        self.types = types
        nbs = Cs[0]
        Vc = len(nbs)
        self.Vc = Vc
        V = n * Vc
        self.V = V
        nb = [[-1] * 4 for _ in range(V)]
        for q in range(n):
            for c in range(Vc):
                for i in range(4):
                    d = nbs[c][i]
                    if d >= 0:
                        nb[q * Vc + c][i] = act[i][q] * Vc + d
        self.nb = nb
        Vb = len(Cb[0])
        self.m = [q * Vb + io[c] for q in range(n) for c in range(Vc)]
        # fibres of m that are nontrivial, restricted to vertices
        fib = {}
        for v in range(V):
            fib.setdefault(self.m[v], []).append(v)
        self.kfib = [vs for vs in fib.values() if len(vs) > 1]
        self.seeds = []   # (q, typeindex, pair of vertices)
        for q in range(n):
            for ti, ((c, d), law, sz) in enumerate(types):
                self.seeds.append((q, ti, law, (q * Vc + c, q * Vc + d)))

    def closure(self, pairs):
        par = list(range(self.V))
        nb = self.nb
        adj = {}

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x

        def nbr(r):
            a = adj.get(r)
            return a if a is not None else nb[r]
        stack = list(pairs)
        while stack:
            x, y = stack.pop()
            x, y = find(x), find(y)
            if x == y:
                continue
            par[y] = x
            ax, ay = nbr(x), nbr(y)
            new = list(ax)
            for i in range(4):
                if ay[i] >= 0:
                    if new[i] >= 0:
                        stack.append((new[i], ay[i]))
                    else:
                        new[i] = ay[i]
            adj[x] = new
            if y in adj:
                del adj[y]
        return [find(v) for v in range(self.V)]

    def promotes(self, cls):
        for vs in self.kfib:
            c = cls[vs[0]]
            for v in vs:
                if cls[v] != c:
                    return False
        return True


_MODELS = {}


def model(j):
    if j not in _MODELS:
        Cb = core(j)
        Cs = core(j + 1)
        io = iota(Cs, Cb)
        _MODELS[j] = (Cs, Cb, io, pair_types(Cs, io))
    return _MODELS[j]


if __name__ == '__main__':
    for j in range(5):
        Cs, Cb, io, ty = model(j)
        print('j', j, '|C_j+1|', len(Cs[0]), '|C_j|', len(Cb[0]),
              'unordered types', len(ty), 'lawful', sum(1 for x in ty if x[1]),
              'lawful sizes', [x[2] for x in ty if x[1]],
              'max overfold size', max([x[2] for x in ty if not x[1]] or [0]))
