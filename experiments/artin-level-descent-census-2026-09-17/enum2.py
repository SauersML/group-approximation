"""Exhaustive 2-dimensional representations over F_l of A_Gamma, for two-block dead cuts.

For each representation pi (up to conjugating the first vertex) we compute
  c0 = dim of the common column kernel of the pi(sigma_rho) over F_l
       (c0 > 0 certifies that L_0 is not onto over Z[H]);
  ct = dim of the common column kernel over F_l(t) of pi(sigma_rho)(t^chi(p) pi(p) - 1)
       (ct > 0 certifies [chi] not in Sigma^1).
Only r = 2 (two blocks) is handled, where L_0 onto iff the stacked sigma's have full rank.
ct is computed exactly with polynomial matrices over F_l[t] (python-flint nmod_poly).
"""
import itertools
import sys

import numpy as np
import flint

from census import instance_data, is_star


def setup(l):
    mats = [e for e in itertools.product(range(l), repeat=4) if (e[0] * e[3] - e[1] * e[2]) % l]
    M = np.array(mats, dtype=np.int64).reshape(-1, 2, 2)
    N = len(M)
    w = np.array([l ** 3, l ** 2, l, 1])
    lookup = -np.ones(l ** 4, dtype=np.int64)
    for i, m in enumerate(M):
        lookup[int(m.flatten() @ w)] = i
    T = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        pr = np.einsum('ij,bjk->bik', M[i], M) % l
        T[i] = lookup[pr.reshape(N, 4) @ w]
    return M, T


class Group:
    def __init__(self, l, kmax):
        self.l = l
        self.M, self.T = setup(l)
        self.N = len(self.M)
        self.P = {1: np.arange(self.N)}
        for k in range(2, kmax + 1):
            self.P[k] = self.T[self.P[k - 1], np.arange(self.N)]
        self.Ssing = {}
        self.Smat = {}

    def alt(self, x, y, m):
        """alternating product x y x ... of length m; x scalar index, y array."""
        k = m // 2
        xy = self.T[x, y]
        pw = self.P[k][xy] if k >= 1 else None
        if m % 2 == 0:
            return pw
        if k == 0:
            return np.full_like(y, x)
        return self.T[pw, x]

    def alt_r(self, y, x, m):
        """alternating product y x y ... of length m; y array, x scalar."""
        k = m // 2
        yx = self.T[y, x]
        pw = self.P[k][yx] if k >= 1 else None
        if m % 2 == 0:
            return pw
        if k == 0:
            return y
        return self.T[pw, y]

    def S(self, k):
        if k not in self.Smat:
            l = self.l
            R = np.broadcast_to(np.eye(2, dtype=np.int64), (self.N, 2, 2)).copy()
            Pm = R.copy()
            for _ in range(k - 1):
                Pm = np.einsum('bij,bjk->bik', Pm, self.M) % l
                R = (R + Pm) % l
            self.Smat[k] = R
            d = (R[:, 0, 0] * R[:, 1, 1] - R[:, 0, 1] * R[:, 1, 0]) % l
            self.Ssing[k] = d == 0
        return self.Smat[k]


def rank_mod(A, l):
    A = A.copy() % l
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i, c] % l), None)
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), l - 2, l)) % l
        for i in range(rows):
            if i != r and A[i, c]:
                A[i] = (A[i] - A[i, c] * A[r]) % l
        r += 1
    return r


def poly_rank(rows, l):
    """rank over F_l(t) of a matrix given as list of lists of flint.nmod_poly."""
    A = [list(r) for r in rows]
    nr, nc = len(A), len(A[0])
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if not A[i][c].is_zero()), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(nr):
            if i != r and not A[i][c].is_zero():
                a, b = A[r][c], A[i][c]
                A[i] = [a * A[i][j] - b * A[r][j] for j in range(nc)]
        r += 1
    return r


def ct_dim(blocks_data, l):
    """blocks_data: list of (S (2x2 ints), U (2x2 ints), e = chi(p))."""
    t = flint.nmod_poly([0, 1], l)
    rows = []
    for S, U, e in blocks_data:
        te = t ** e
        G = [[flint.nmod_poly([int(U[i][j])], l) * te - (1 if i == j else 0) for j in range(2)]
             for i in range(2)]
        for i in range(2):
            rows.append([sum((flint.nmod_poly([int(S[i][m])], l) * G[m][j] for m in range(2)),
                             flint.nmod_poly([0], l)) for j in range(2)])
    return 2 - poly_rank(rows, l)


def enumerate_reps(V, E, chi, l, grp=None, limit=None, verbose=False):
    comp, blocks, cross = instance_data(V, E, chi)
    assert len(blocks) == 2, "only two blocks handled"
    kmax = max([l_ // 2 + 1 for l_ in E.values()] + [2])
    G = grp or Group(l, kmax)
    for k in set(k for _, _, k in cross):
        G.S(k)
    # order vertices greedily by adjacency
    order = [V[0]]
    rest = list(V[1:])
    while rest:
        best = max(rest, key=lambda v: sum(1 for u in order if (u, v) in E or (v, u) in E))
        order.append(best)
        rest.remove(best)
    lab = {}
    for (a, b), m in E.items():
        lab[(a, b)] = m
        lab[(b, a)] = m
    crossk = {}
    for p, q, k in cross:
        crossk[(p, q)] = k
    ident = int(np.argmax(np.all(G.M == np.eye(2, dtype=np.int64), axis=(1, 2))))
    inv = np.argmax(G.T == ident, axis=1)
    seen = np.zeros(G.N, bool)
    reps0 = []
    for i in range(G.N):
        if not seen[i]:
            reps0.append(i)
            seen[G.T[G.T[np.arange(G.N), i], inv]] = True
    allidx = np.arange(G.N)
    stats = {"reps": 0, "c0pos": 0, "ctpos": 0, "c0_not_ct": 0}
    examples = {"c0_not_ct": [], "ctpos": []}

    def candidates(assign, v):
        c = allidx
        for u, x in assign.items():
            m = lab.get((u, v))
            if m is None:
                continue
            c = c[G.alt(x, c, m) == G.alt_r(c, x, m)]
            if len(c) == 0:
                return c
        for u, x in assign.items():
            if (u, v) in crossk:  # u = p, v = q ; sigma = S_k(pq)
                k = crossk[(u, v)]
                c = c[G.Ssing[k][G.T[x, c]]]
            elif (v, u) in crossk:
                k = crossk[(v, u)]
                c = c[G.Ssing[k][G.T[c, x]]]
        return c

    def finish(assign):
        stats["reps"] += 1
        Sb = []
        for p, q, k in cross:
            Sm = G.Smat[k][G.T[assign[p], assign[q]]]
            Sb.append((Sm, G.M[assign[p]], chi[p]))
        c0 = 2 - rank_mod(np.vstack([s for s, _, _ in Sb]), l)
        if c0 == 0:
            return
        stats["c0pos"] += 1
        ct = ct_dim(Sb, l)
        if ct > 0:
            stats["ctpos"] += 1
            if len(examples["ctpos"]) < 2:
                examples["ctpos"].append({v: G.M[assign[v]].tolist() for v in V})
        else:
            stats["c0_not_ct"] += 1
            if len(examples["c0_not_ct"]) < 3:
                examples["c0_not_ct"].append(({v: G.M[assign[v]].tolist() for v in V}, c0))

    def rec(i, assign):
        if limit and stats["reps"] >= limit:
            return
        if i == len(order):
            finish(assign)
            return
        v = order[i]
        cs = reps0 if i == 0 else candidates(assign, v)
        for x in cs:
            assign[v] = int(x)
            rec(i + 1, assign)
            del assign[v]

    rec(0, {})
    return stats, examples, cross


if __name__ == "__main__":
    pass
