"""Independent panel checker (cube-complex lens), 2026-09-16.
Shares no code with experiments/zaremsky-4-05-jensen-cube-2026-09-16/.

Builds finite median graphs from explicit constructions (products of trees/paths,
grids, cubes, convex hulls of finite sets in RAAG Cayley graphs, Buneman graphs of
random split systems), verifies the median property by brute force, computes
Djokovic-Winkler hyperplanes from BFS distances, verifies d = Hamming distance,
enumerates coordinate cubes, empty quadrants, and provides LP helpers over the
box E=[0,1]^H and over |X| (union of maximal cubes).
"""
import itertools, random
from collections import deque
import numpy as np
from scipy.optimize import linprog


def bfs_dist(adj):
    n = len(adj)
    D = np.full((n, n), -1, dtype=int)
    for s in range(n):
        D[s, s] = 0
        q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if D[s, y] < 0:
                    D[s, y] = D[s, x] + 1
                    q.append(y)
    return D


class MG:
    def __init__(self, adj, name="", check=True):
        self.name = name
        self.adj = [sorted(set(a)) for a in adj]
        n = self.n = len(adj)
        D = self.D = bfs_dist(self.adj)
        assert (D >= 0).all(), "disconnected"
        # Djokovic-Winkler: split of edge uv is W_uv = {x : d(x,u) < d(x,v)}
        splits = {}
        for u in range(n):
            for v in self.adj[u]:
                if u < v:
                    W = D[:, u] < D[:, v]
                    key = tuple(W) if not W[0] else tuple(~W)  # side NOT containing base 0 -> h^1
                    splits.setdefault(key, []).append((u, v))
        self.H = [np.array(k, dtype=bool) for k in splits]
        self.m = len(self.H)
        self.C = np.array([[int(self.H[h][x]) for h in range(self.m)] for x in range(n)], dtype=int)
        ham = (self.C[:, None, :] != self.C[None, :, :]).sum(axis=2)
        self.hamming_ok = bool((ham == D).all())
        self.median_ok = self.check_median() if check else None
        self.vset = {tuple(r): i for i, r in enumerate(self.C)}
        self.cubes()
        self.quadrants()

    def check_median(self):
        D = self.D
        n = self.n
        I = (D[:, :, None] + D[None, :, :] == D[:, None, :])  # I[a,x,b]
        for a in range(n):
            for b in range(a, n):
                Iab = I[a, :, b]
                # for all c: count x with x in I(a,b), I(b,c), I(a,c)
                cnt = (Iab[None, :] & I[b, :, :].T & I[a, :, :].T).sum(axis=1)
                if (cnt != 1).any():
                    return False
        return True

    def cubes(self):
        """All coordinate cubes, as (base coordinate tuple with F coords 0, F)."""
        m = self.m
        found = set()
        for x in range(self.n):
            v = tuple(self.C[x])
            stack = [()]
            while stack:
                F = stack.pop()
                base = list(v)
                for h in F:
                    base[h] = 0
                key = (tuple(base), F)
                if key in found:
                    continue
                found.add(key)
                for h in range(m):
                    if h in F:
                        continue
                    F2 = tuple(sorted(F + (h,)))
                    ok = True
                    for sig in itertools.product((0, 1), repeat=len(F2)):
                        u = list(v)
                        for g, b in zip(F2, sig):
                            u[g] = b
                        if tuple(u) not in self.vset:
                            ok = False
                            break
                    if ok:
                        stack.append(F2)
        self.allcubes = found
        self.k = max(len(F) for _, F in found)
        maxc = []
        for base, F in found:
            is_max = False
            for h in range(m):
                if h in F:
                    continue
                F2 = tuple(sorted(F + (h,)))
                b2 = list(base)
                b2[h] = 0
                if (tuple(b2), F2) in found:
                    is_max = True
                    break
            if not is_max:
                maxc.append((base, F))
        self.maxcubes = maxc

    def quadrants(self):
        """Empty quadrants (h,a,g,b): halfspace h^a and g^b disjoint, h<g."""
        Q = []
        for h in range(self.m):
            for g in range(h + 1, self.m):
                for a in (0, 1):
                    for b in (0, 1):
                        if not ((self.C[:, h] == a) & (self.C[:, g] == b)).any():
                            Q.append((h, a, g, b))
        self.Q = Q

    # ---- geometry -----
    def Lcoef(self, x):
        """L_x(p) = sum_h |c_x(h) - p_h| = a.p + const on the box."""
        c = self.C[x]
        return (1 - 2 * c).astype(float), float(c.sum())

    def in_X(self, p, tol=1e-9):
        F = tuple(h for h in range(self.m) if tol < p[h] < 1 - tol)
        base = [int(round(p[h])) if h not in F else 0 for h in range(self.m)]
        for sig in itertools.product((0, 1), repeat=len(F)):
            u = list(base)
            for g, b in zip(F, sig):
                u[g] = b
            if tuple(u) not in self.vset:
                return False
        return True

    def star(self, p, tol=1e-9):
        """max over empty quadrants of min charge."""
        worst = 0.0
        for (h, a, g, b) in self.Q:
            qa = p[h] if a == 1 else 1 - p[h]
            qb = p[g] if b == 1 else 1 - p[g]
            worst = max(worst, min(qa, qb))
        return worst

    def lp_minmax_box(self, centres, rho):
        """min over c in E of max_i (L_{z_i}(c) - rho_i)."""
        m = self.m
        A, bub = [], []
        for z, r in zip(centres, rho):
            a, const = self.Lcoef(z)
            A.append(list(a) + [-1.0])
            bub.append(r - const)
        cvec = np.zeros(m + 1)
        cvec[-1] = 1
        res = linprog(cvec, A_ub=np.array(A), b_ub=np.array(bub),
                      bounds=[(0, 1)] * m + [(None, None)], method="highs")
        return res.fun, res.x[:m]

    def lp_minmax_X(self, centres, rho):
        """min over p in |X| of max_i (L_{z_i}(p) - rho_i), by LP on every maximal cube."""
        best, bestp = np.inf, None
        rows = [self.Lcoef(z) for z in centres]
        for base, F in self.maxcubes:
            Fl = list(F)
            A, bub = [], []
            for (a, const), r in zip(rows, rho):
                fixed = const + sum(a[h] * base[h] for h in range(self.m) if h not in F)
                A.append([a[h] for h in Fl] + [-1.0])
                bub.append(r - fixed)
            cvec = np.zeros(len(Fl) + 1)
            cvec[-1] = 1
            res = linprog(cvec, A_ub=np.array(A), b_ub=np.array(bub),
                          bounds=[(0, 1)] * len(Fl) + [(None, None)], method="highs")
            if res.fun < best:
                best = res.fun
                p = np.array(base, dtype=float)
                for i, h in enumerate(Fl):
                    p[h] = res.x[i]
                bestp = p
        return best, bestp

    def random_point_X(self, rng, dyadic=None):
        base, F = rng.choice(self.maxcubes)
        p = np.array(base, dtype=float)
        for h in F:
            if dyadic:
                p[h] = rng.randint(0, dyadic) / dyadic
            else:
                p[h] = rng.random()
        return p


# ------------------------------------------------------------------ constructions
def product(adj1, adj2):
    n1, n2 = len(adj1), len(adj2)
    idx = lambda i, j: i * n2 + j
    adj = [[] for _ in range(n1 * n2)]
    for i in range(n1):
        for j in range(n2):
            for i2 in adj1[i]:
                adj[idx(i, j)].append(idx(i2, j))
            for j2 in adj2[j]:
                adj[idx(i, j)].append(idx(i, j2))
    return adj


def path(n):
    return [[j for j in (i - 1, i + 1) if 0 <= j < n] for i in range(n)]


def star(n):  # K_{1,n}
    adj = [list(range(1, n + 1))] + [[0] for _ in range(n)]
    return adj


def tree_from_parents(par):
    n = len(par) + 1
    adj = [[] for _ in range(n)]
    for i, p in enumerate(par, start=1):
        adj[i].append(p)
        adj[p].append(i)
    return adj


def random_tree(rng, n):
    return tree_from_parents([rng.randrange(i) for i in range(1, n)])


# ----- RAAG Cayley graph hulls
class RAAG:
    def __init__(self, nv, edges):
        self.nv = nv
        self.E = set()
        for a, b in edges:
            self.E.add((a, b))
            self.E.add((b, a))
        self.letters = [(g, e) for g in range(nv) for e in (1, -1)]

    def comm(self, x, y):
        return x[0] != y[0] and (x[0], y[0]) in self.E

    def reduce(self, w):
        w = list(w)
        changed = True
        while changed:
            changed = False
            for i in range(len(w)):
                for j in range(i + 1, len(w)):
                    if w[j] == (w[i][0], -w[i][1]):
                        if all(self.comm(w[i], w[t]) for t in range(i + 1, j)):
                            del w[j]
                            del w[i]
                            changed = True
                            break
                    if not self.comm(w[i], w[j]):
                        break
                if changed:
                    break
        return w

    def nf(self, w):
        w = self.reduce(w)
        out = []
        while w:
            cands = []
            for p in range(len(w)):
                if all(self.comm(w[p], w[t]) for t in range(p)):
                    cands.append((w[p], p))
            letter, p = min(cands)
            out.append(letter)
            del w[p]
        return tuple(out)

    def inv(self, w):
        return tuple((g, -e) for g, e in reversed(w))

    def dist(self, a, b):
        return len(self.reduce(self.inv(a) + b))

    def interval(self, a, b, memo):
        key = (a, b)
        if key in memo:
            return memo[key]
        d = self.dist(a, b)
        res = {a}
        if d > 0:
            for s in self.letters:
                as_ = self.nf(a + (s,))
                if self.dist(as_, b) == d - 1:
                    res |= self.interval(as_, b, memo)
        memo[key] = res
        return res

    def hull(self, S):
        K = set(self.nf(s) for s in S)
        memo = {}
        while True:
            new = set(K)
            L = sorted(K)
            for i in range(len(L)):
                for j in range(i + 1, len(L)):
                    new |= self.interval(L[i], L[j], memo)
            if new == K:
                return sorted(K)
            K = new

    def graph(self, K):
        idx = {g: i for i, g in enumerate(K)}
        adj = [[] for _ in K]
        for g in K:
            for s in self.letters:
                h = self.nf(g + (s,))
                if h in idx:
                    adj[idx[g]].append(idx[h])
        return adj

    def random_word(self, rng, L):
        return self.nf([rng.choice(self.letters) for _ in range(L)])


def buneman(rng, npts, nsplits):
    pts = frozenset(range(npts))
    splits = set()
    tries = 0
    while len(splits) < nsplits and tries < 2000:
        tries += 1
        A = frozenset(p for p in pts if rng.random() < 0.5)
        if 0 < len(A) < npts:
            B = pts - A
            splits.add(min((A, B), key=lambda s: sorted(s)))
    splits = list(splits)
    V = []
    for sig in itertools.product((0, 1), repeat=len(splits)):
        ch = [splits[h] if sig[h] else pts - splits[h] for h in range(len(splits))]
        if all(ch[i] & ch[j] for i in range(len(ch)) for j in range(i)):
            V.append(sig)
    vset = {v: i for i, v in enumerate(V)}
    adj = [[] for _ in V]
    for i, v in enumerate(V):
        for h in range(len(v)):
            u = list(v)
            u[h] ^= 1
            u = tuple(u)
            if u in vset:
                adj[i].append(vset[u])
    return adj
