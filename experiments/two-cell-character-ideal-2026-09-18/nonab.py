# Non-abelian tests for a two-cell configuration (lane w10-048).
# The cylinder row c = g d u_0 - d u_1 in ZG^B (eps = 1) as signed words: for each basis (non-tree) edge e,
# every crossing of e by the path of w contributes +-(tree path to start) * (prefix of w up to the origin of e);
# the common right factor tau_{o(e)}^{-1} per coordinate is a unit and is dropped.
# For a permutation representation rho: G -> S_k (right action, R_{uv} = R_u R_v) the row is killed
# (not surjective M^B -> M) iff rank [rho(c_1) ... rho(c_B)] < k over the field.
import itertools, sys
from fc import *


def tree_words(tr, v0, n):
    tw = {v0: []}; q = [v0]; tree = set()
    while q:
        u = q.pop()
        for l in range(4):
            r = tr.get((u, l))
            if r and r[0] not in tw: tw[r[0]] = tw[u] + [l]; tree.add(r[1]); q.append(r[0])
    return tw, tree


def crow_words(edges, tr, v0, v1, w):
    tw, tree = tree_words(tr, v0, None)
    basis = [i for i in range(len(edges)) if i not in tree]
    def fox(v):
        d = {i: [] for i in basis}; pre = list(tw[v])
        for l in w:
            v2, i, sg = tr[(v, l)]
            if i in d:
                if sg == 1: d[i].append((1, list(pre)))
                else: d[i].append((-1, pre + [l]))
            pre = pre + [l]; v = v2
        return d
    d0 = fox(v0); d1 = fox(v1); g = tw[v1]
    c = {i: [(sg, g + wd) for sg, wd in d0[i]] + [(-sg, wd) for sg, wd in d1[i]] for i in basis}
    return basis, c, g, tw


def perm_word(X, Y, wd, k):
    P = {0: X, 1: Y, 2: [X.index(i) for i in range(k)], 3: [Y.index(i) for i in range(k)]}
    cur = list(range(k))
    for l in wd: cur = [P[l][cur[i]] for i in range(k)]
    return cur   # cur[i] = i^word (right action)


def reps(w, k):
    """x canonical per cycle type, y arbitrary; yield (X, Y) with w(X,Y) = 1 and <X,Y> transitive."""
    def parts(n, m=None):
        if n == 0: yield []; return
        m = m or n
        for i in range(min(n, m), 0, -1):
            for p in parts(n - i, i): yield [i] + p
    for pt in parts(k):
        X = [0] * k; s = 0
        for L in pt:
            for j in range(L): X[s + j] = s + (j + 1) % L
            s += L
        for Y in itertools.permutations(range(k)):
            Y = list(Y)
            if perm_word(X, Y, w, k) != list(range(k)): continue
            seen = {0}; q = [0]
            while q:
                u = q.pop()
                for v in (X[u], Y[u], X.index(u), Y.index(u)):
                    if v not in seen: seen.add(v); q.append(v)
            if len(seen) == k: yield X, Y


def row_rank(c, basis, X, Y, k, p):
    import flint
    M = flint.nmod_mat(k, k * len(basis), p)
    for bi, e in enumerate(basis):
        for sg, wd in c[e]:
            pw = perm_word(X, Y, wd, k)
            for i in range(k): M[i, bi * k + pw[i]] = (int(M[i, bi * k + pw[i]]) + sg) % p
    return M.rank()
