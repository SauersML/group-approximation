"""Continuous refinement of pivot paths in X_n (library + CLI).

A path is P = z_0, z_1, ..., z_k, z_{k+1} = rho P with z_i a nonnegative combination of the unit vectors of the
vertices of a chain sigma_i. Consecutive chains must lie in a common noncrossing spanning tree (checked exactly by
tree search), so each segment is a geodesic inside an X-apartment and the length is an upper bound for d_X.
"""
import math, sys, itertools
import numpy as np
from scipy.optimize import minimize
from ncp_lib import *


def make(n):
    m = n - 1

    def cosd(x, z):
        a, b = rank(x), rank(z)
        k = n - nblocks(x) - nblocks(z) + nblocks(join_P(x, z))
        return (k - a * b / m) / math.sqrt((a - a * a / m) * (b - b * b / m))
    return cosd


def parse(s, n):
    groups = [tuple(int(c) - 1 for c in blk) for blk in s.strip('{}').split(',') if blk]
    return canon(groups + [(i,) for i in range(n) if not any(i in g for g in groups)], n)


def fmt(p):
    return '{' + ','.join(''.join(str(x + 1) for x in b) for b in blocks(p) if len(b) > 1) + '}'


def common_tree(parts, n):
    """Is there a noncrossing spanning tree in which every block of every partition in parts is connected?
    Search: blocks must be connected; add edges greedily by backtracking over chords (small n only)."""
    blks = set()
    for p in parts:
        for b in blocks(p):
            if len(b) > 1:
                blks.add(frozenset(b))
    blks = sorted(blks, key=len)
    edges = list(itertools.combinations(range(n), 2))

    def cross(e, f):
        a, b = e; c, d = f
        if len({a, b, c, d}) < 4:
            return False
        return (a < c < b) != (a < d < b)

    def connected(B, E):
        B = list(B); seen = {B[0]}; st = [B[0]]
        while st:
            u = st.pop()
            for a, b in E:
                for x, y in ((a, b), (b, a)):
                    if x == u and y in B and y not in seen:
                        seen.add(y); st.append(y)
        return len(seen) == len(B)

    def comp(E):
        par = list(range(n))
        def f(x):
            while par[x] != x:
                x = par[x]
            return x
        for a, b in E:
            ra, rb = f(a), f(b)
            if ra != rb:
                par[ra] = rb
        return f
    # backtracking: choose edges inside blocks (forest), then complete arbitrarily
    def rec(E, k):
        if k == len(blks):
            return complete(E)
        B = blks[k]
        if connected(B, E):
            return rec(E, k + 1)
        f = comp(E)
        for e in itertools.combinations(sorted(B), 2):
            if f(e[0]) != f(e[1]) and all(not cross(e, g) for g in E):
                r = rec(E + [e], k)
                if r is not None:
                    return r
        return None

    def complete(E):
        # add chords keeping acyclic and noncrossing and not creating new connections inside blocks improperly:
        # a block stays connected under adding edges; but adding an edge between two vertices of a block that are
        # already connected is a cycle (forbidden). Connecting outside is fine as long as blocks remain induced-connected,
        # which only fails if a new edge joins... induced connectivity is monotone in edges, so any completion works.
        f = comp(E)
        for e in edges:
            if f(e[0]) != f(e[1]) and all(not cross(e, g) for g in E):
                E = E + [e]; f = comp(E)
        return E if len(E) == n - 1 else None
    return rec([], 0)


def path_length(faces, lams, G, vid):
    zs = []
    for f, lam in zip(faces, lams):
        zs.append((f, lam))
    tot = 0.0
    for (f, a), (g, b) in zip(zs, zs[1:]):
        A = np.array([vid[v] for v in f]); B = np.array([vid[v] for v in g])
        num = a @ G[np.ix_(A, B)] @ b
        na = math.sqrt(a @ G[np.ix_(A, A)] @ a); nb = math.sqrt(b @ G[np.ix_(B, B)] @ b)
        tot += math.acos(max(-1, min(1, num / (na * nb))))
    return tot


def optimise(faces, n, restarts=20, seed=0):
    cosd = make(n)
    verts = sorted({v for f in faces for v in f})
    vid = {v: i for i, v in enumerate(verts)}
    G = np.array([[cosd(a, b) for b in verts] for a in verts])
    sizes = [len(f) for f in faces]
    rng = np.random.default_rng(seed)

    def split(x):
        out, k = [], 0
        for s in sizes:
            out.append(np.abs(x[k:k + s]) + 1e-15); k += s
        return out

    def obj(x):
        return path_length(faces, split(x), G, vid)
    best = None
    for r in range(restarts):
        x0 = rng.random(sum(sizes)) + 0.01
        res = minimize(obj, x0, method='L-BFGS-B', bounds=[(0, None)] * len(x0))
        if best is None or res.fun < best.fun:
            best = res
    return best.fun, split(best.x)


if __name__ == '__main__':
    n = int(sys.argv[1])
    faces = [tuple(parse(s, n) for s in grp.split('<')) for grp in sys.argv[2:]]
    for f, g in zip(faces, faces[1:]):
        T = common_tree(list(f) + list(g), n)
        print('common tree', [fmt(x) for x in f], [fmt(x) for x in g], T)
        assert T is not None
    L, lams = optimise(faces, n)
    print('length', L / math.pi, 'pi')
    for f, lam in zip(faces, lams):
        print('  ', [(fmt(v), round(float(l), 4)) for v, l in zip(f, lam)])
