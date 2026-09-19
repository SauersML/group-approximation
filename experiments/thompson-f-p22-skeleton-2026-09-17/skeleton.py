#!/usr/bin/env python3
"""Exact doubling ratios of Guba's monomial sets on thin universes of tuples.

Tuple model (thompson-f-p22-cylinder-functional-needs-thin-skeletons, item 1): S = S(n -> k) acts on
T^n by the ways of adding d = n - k carets to roots 0..n-1, and h(S) = inf |S A| / |A| over finite
nonempty A in T^n.  For a universe U (tuples with N carets whose entries lie in a tree class C) we
compute EXACTLY

    rho(U) = min { |S A| / |A| : nonempty A subset U }

by parametric min cut (source -> a cap K, a -> image cap inf, image -> sink cap J; Dinkelbach on
K/J).  Images are computed in full (they need not lie in any class), so every value is a rigorous
upper bound for h(S), witnessed by the returned set A.

Tree classes: 'all', 'vine' (left and right vines), 'cat' (caterpillars: every caret has a leaf
child), 'w<m>' (every caret has a child with at most m carets).
"""
import itertools, sys, collections
from fractions import Fraction
from functools import lru_cache
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_flow, breadth_first_order

LEAF = 0


def carets(t):
    return 0 if t == LEAF else 1 + carets(t[0]) + carets(t[1])


def strahler(t):
    """Horton-Strahler number with leaf = 0 (so caterpillars with >= 1 caret have strahler 1)."""
    if t == LEAF:
        return 0
    a, b = strahler(t[0]), strahler(t[1])
    return a + 1 if a == b else max(a, b)


@lru_cache(maxsize=None)
def trees_in(cls, c):
    if c == 0:
        return (LEAF,)
    if cls == 'vine':
        L, R = LEAF, LEAF
        for _ in range(c):
            L, R = (L, LEAF), (LEAF, R)
        return (L,) if c == 1 else (L, R)
    if cls in ('L', 'R'):
        t = LEAF
        for _ in range(c):
            t = (t, LEAF) if cls == 'L' else (LEAF, t)
        return (t,)
    if cls.startswith('st'):
        return tuple(t for t in trees_in('all', c) if strahler(t) <= int(cls[2:]))
    if cls == 'all':
        w = c
    elif cls == 'cat':
        w = 0
    elif cls.startswith('w'):
        w = int(cls[1:])
    else:
        raise ValueError(cls)
    out = []
    for i in range(c):
        j = c - 1 - i
        if min(i, j) > w:
            continue
        for u in trees_in(cls, i):
            for v in trees_in(cls, j):
                out.append((u, v))
    return tuple(out)


def merge_maps(n, k):
    """All distinct ways of adding n-k carets to n roots leaving k roots, as symbolic forests."""
    d = n - k
    seen = set()
    out = []
    for word in itertools.product(range(n), repeat=d):
        f = list(range(n))
        ok = True
        for j in word:
            if j + 1 >= len(f):
                ok = False
                break
            f = f[:j] + [(f[j], f[j + 1])] + f[j + 2:]
        if ok:
            key = tuple(f)
            if key not in seen:
                seen.add(key)
                out.append(key)
    return out


def instantiate(sym, a):
    if isinstance(sym, int):
        return a[sym]
    return (instantiate(sym[0], a), instantiate(sym[1], a))


def universe(n, N, cls, entry_classes=None):
    out = []
    for comp in itertools.product(range(N + 1), repeat=n):
        if sum(comp) != N:
            continue
        pools = [trees_in(entry_classes[i] if entry_classes else cls, c) for i, c in enumerate(comp)]
        out.extend(itertools.product(*pools))
    return out


def min_ratio(edges, nl, ni):
    """edges: int array (m,2) of (left, image), deduplicated.  Returns (Fraction, left index list)."""
    ratio = Fraction(ni, nl)
    A = list(range(nl))
    src, snk = nl + ni, nl + ni + 1
    V = nl + ni + 2
    while True:
        K, J = ratio.numerator, ratio.denominator
        INF = min(K * nl + 1, 2 ** 31 - 1)
        rows = np.concatenate([np.full(nl, src), edges[:, 0], nl + np.arange(ni)])
        cols = np.concatenate([np.arange(nl), nl + edges[:, 1], np.full(ni, snk)])
        caps = np.concatenate([np.full(nl, K), np.full(len(edges), INF), np.full(ni, J)])
        m = csr_matrix((caps.astype(np.int32), (rows, cols)), shape=(V, V))
        res = maximum_flow(m, src, snk, method='dinic')
        if K * nl - res.flow_value <= 0:
            return ratio, A
        resid = (m - res.flow).tocsr()
        resid.data = (resid.data > 0).astype(np.int8)
        resid.eliminate_zeros()
        reach = breadth_first_order(resid, src, directed=True, return_predecessors=False)
        side = np.zeros(V, bool)
        side[reach] = True
        A = [i for i in range(nl) if side[i]]
        sel = side[edges[:, 0]]
        img = np.unique(edges[sel, 1])
        new = Fraction(len(img), len(A))
        assert new < ratio
        ratio = new


def evaluate(n, k, U):
    maps = merge_maps(n, k)
    img_id = {}
    e = []
    for ai, a in enumerate(U):
        for s in maps:
            g = tuple(instantiate(x, a) for x in s)
            e.append((ai, img_id.setdefault(g, len(img_id))))
    edges = np.unique(np.array(e, dtype=np.int64), axis=0)
    r, A = min_ratio(edges, len(U), len(img_id))
    return r, [U[i] for i in A], len(img_id)


if __name__ == "__main__":
    n, k = int(sys.argv[1]), int(sys.argv[2])
    cls = sys.argv[3]
    ec = cls.split('/') if '/' in cls else None
    Ns = [int(x) for x in sys.argv[4].split(',')]
    for N in Ns:
        U = universe(n, N, cls, ec)
        r, A, ni = evaluate(n, k, U)
        print(f"S({n}->{k}) class={cls} N={N} |U|={len(U)} images={ni} rho={r} ~{float(r):.6f} |A|={len(A)}",
              flush=True)
