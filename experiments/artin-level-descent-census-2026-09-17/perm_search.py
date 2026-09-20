"""Search for a *twisted* witness (ct > 0) for the census2 CANDIDATE among permutation
representations G -> S_n.  G: vertices a,b,c,d,e; labels ab 6, ac 4, ad 4, ae 10, bc 3, bd 4,
be 2, ce 2 (cd, de free); chi = (a,b,c,d,e) = (1,-1,-1,1,-1).  Cross edges (p,q,half):
ab 3, ac 2, ae 5, db 2.  Blocks: S_k(pq) (s P(p) - 1).
A permutation matrix rep is defined over Z; ct is tested by the rank at random s over F_P,
P = 1000003 (rank deficiency at 3 random points => reported, then checked exactly with sympy).
Usage: python3 perm_search.py n [maxhoms]"""
import itertools
import sys
from math import gcd

import numpy as np

V = ['a', 'b', 'c', 'd', 'e']
E = {('a', 'b'): 6, ('a', 'c'): 4, ('a', 'd'): 4, ('a', 'e'): 10, ('b', 'c'): 3, ('b', 'd'): 4,
     ('b', 'e'): 2, ('c', 'e'): 2}
CROSS = [('a', 'b', 3), ('a', 'c', 2), ('a', 'e', 5), ('d', 'b', 2)]
ORDER = ['a', 'b', 'c', 'e', 'd']
P = 1000003


def build(n):
    perms = list(itertools.permutations(range(n)))
    idx = {p: i for i, p in enumerate(perms)}
    A = np.array(perms, dtype=np.int16)
    N = len(perms)
    # T[i, j] = perm_i o perm_j  (apply j first):  (i o j)(x) = i[j[x]]
    T = np.empty((N, N), dtype=np.int32)
    mult = np.array([n ** (n - 1 - k) for k in range(n)], dtype=np.int64)
    code = {int((np.array(p) * mult).sum()): i for i, p in enumerate(perms)}
    keys = np.array(sorted(code)), None
    lut_keys = np.array(sorted(code))
    lut_vals = np.array([code[k] for k in lut_keys])
    for i in range(N):
        comp = A[i][A]  # comp[j] = perm_i[perm_j]
        c = (comp.astype(np.int64) * mult).sum(axis=1)
        T[i] = lut_vals[np.searchsorted(lut_keys, c)]
    return perms, T


def cyc_lengths(p):
    n, seen, out = len(p), [False] * len(p), []
    for i in range(n):
        if not seen[i]:
            L, j = 0, i
            while not seen[j]:
                seen[j] = True
                j = p[j]
                L += 1
            out.append(L)
    return out


def alt(T, x, y, m):
    # x y x y ... (m factors), x scalar index, y array of indices
    out = None
    for t in range(m):
        f = x if t % 2 == 0 else y
        if out is None:
            out = np.full_like(y, x) if t % 2 == 0 else y
        else:
            out = T[out, f]
    return out


def alt_r(T, y, x, m):
    out = None
    for t in range(m):
        f = y if t % 2 == 0 else x
        if out is None:
            out = y.copy()
        else:
            out = T[out, f]
    return out


def pmat(p):
    n = len(p)
    M = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        M[p[i], i] = 1
    return M


def rank_modP(A):
    A = A.copy() % P
    r, (rows, cols) = 0, A.shape
    for c in range(cols):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), P - 2, P)) % P
        f = A[:, c].copy()
        f[r] = 0
        A = (A - np.outer(f, A[r])) % P
        r += 1
        if r == rows:
            break
    return r


def blocks(rep, perms):
    n = len(perms[0])
    M = {v: pmat(perms[rep[v]]) for v in V}
    out = []
    for p, q, k in CROSS:
        X = M[p] @ M[q]
        S = np.eye(n, dtype=np.int64)
        Pw = np.eye(n, dtype=np.int64)
        for _ in range(k - 1):
            Pw = Pw @ X
            S = S + Pw
        out.append((S, M[p]))
    return out


def main(n, maxhoms):
    perms, T = build(n)
    N = len(perms)
    lab = {}
    for (x, y), m in E.items():
        lab[(x, y)] = m
        lab[(y, x)] = m
    crossk = {(p, q): k for p, q, k in CROSS}
    cl = [cyc_lengths(p) for p in perms]
    # singular[k][i]: S_k(perm_i) singular over Q  <=> some cycle length L with gcd(L, k) > 1
    sing = {k: np.array([any(gcd(L, k) > 1 for L in c) for c in cl]) for k in set(k for _, _, k in CROSS)}
    # a up to conjugacy: one representative per cycle type
    reps_a, seen = [], set()
    for i, c in enumerate(cl):
        key = tuple(sorted(c))
        if key not in seen:
            seen.add(key)
            reps_a.append(i)
    allidx = np.arange(N)
    stats = {"homs": 0, "c0pos": 0, "twisted_hits": 0}
    hits = []
    rng = np.random.default_rng(1)

    def cands(assign, v):
        c = allidx
        for u, x in assign.items():
            m = lab.get((u, v))
            if m is not None:
                c = c[alt(T, x, c, m) == alt_r(T, c, x, m)]
            if (u, v) in crossk:
                c = c[sing[crossk[(u, v)]][T[x, c]]]
            elif (v, u) in crossk:
                c = c[sing[crossk[(v, u)]][T[c, x]]]
            if len(c) == 0:
                break
        return c

    def finish(assign):
        stats["homs"] += 1
        B = blocks(assign, perms)
        if rank_modP(np.vstack([S for S, _ in B])) == n:
            return
        stats["c0pos"] += 1
        for _ in range(3):
            s = int(rng.integers(2, P - 1))
            Mt = np.vstack([(S @ ((s * U - np.eye(n, dtype=np.int64)) % P)) % P for S, U in B])
            if rank_modP(Mt) == n:
                return
        stats["twisted_hits"] += 1
        if len(hits) < 5:
            hits.append({v: perms[assign[v]] for v in V})

    def rec(i, assign):
        if maxhoms and stats["homs"] >= maxhoms:
            return
        if i == len(ORDER):
            finish(assign)
            return
        v = ORDER[i]
        cs = reps_a if i == 0 else cands(assign, v)
        for x in cs:
            assign[v] = int(x)
            rec(i + 1, assign)
            del assign[v]

    rec(0, {})
    print(f"n={n}", stats, flush=True)
    for h in hits:
        print("  twisted witness candidate:", h, flush=True)


def use_join(h):
    """switch to the 2x2 dead join with halves h = (ac, bc, be, ae), chi = (1, 1, -1, -1)."""
    global V, E, CROSS, ORDER
    V = ['a', 'b', 'c', 'e']
    E = {('a', 'b'): 2, ('c', 'e'): 2, ('a', 'c'): 2 * h[0], ('b', 'c'): 2 * h[1],
         ('b', 'e'): 2 * h[2], ('a', 'e'): 2 * h[3]}
    CROSS = [('a', 'c', h[0]), ('b', 'c', h[1]), ('b', 'e', h[2]), ('a', 'e', h[3])]
    ORDER = ['a', 'c', 'b', 'e']


if __name__ == "__main__":
    n = int(sys.argv[1])
    maxhoms = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    if len(sys.argv) > 3:  # calibration on a 2x2 join, e.g. 2,3,2,4
        use_join(tuple(int(x) for x in sys.argv[3].split(',')))
    main(n, maxhoms)
