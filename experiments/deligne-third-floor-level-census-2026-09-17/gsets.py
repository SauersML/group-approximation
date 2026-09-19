"""Finite Sp_4(Z)-sets from reductions mod N, given as permutations of the five generators."""
import itertools
import numpy as np
from presentation import GEN_INT, J

GINV = [np.rint(np.linalg.inv(g.astype(float))).astype(np.int64) for g in GEN_INT]


def normalize_line(v, p):
    v = [x % p for x in v]
    for x in v:
        if x:
            inv = pow(int(x), -1, p)
            return tuple((y * inv) % p for y in v)
    return None


def orbit(seed, act):
    """BFS orbit of seed under the generators; act(i, pt) -> pt."""
    pts = [seed]
    idx = {seed: 0}
    k = 0
    while k < len(pts):
        x = pts[k]
        k += 1
        for i in range(5):
            y = act(i, x)
            if y not in idx:
                idx[y] = len(pts)
                pts.append(y)
    perm = [[idx[act(i, x)] for x in pts] for i in range(5)]
    return pts, perm


def lines(p):
    def act(i, x):
        return normalize_line(GEN_INT[i] @ np.array(x), p)
    return orbit((1, 0, 0, 0), act)


def vectors(p, seed=(1, 0, 0, 0), N=None):
    N = N or p

    def act(i, x):
        return tuple(int(c) % N for c in GEN_INT[i] @ np.array(x))
    return orbit(tuple(seed), act)


def rref_mod(M, p):
    M = [list(map(lambda c: c % p, row)) for row in M]
    r = 0
    rows, cols = len(M), len(M[0])
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], -1, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return tuple(tuple(row) for row in M[:r])


def lagrangians(p):
    def act(i, L):
        B = np.array(L).T  # columns span
        C = (GEN_INT[i] @ B) % p
        return rref_mod(C.T.tolist(), p)
    seed = rref_mod([[1, 0, 0, 0], [0, 1, 0, 0]], p)  # span(a1, a2) is Lagrangian
    return orbit(seed, act)


def product(A, B):
    """Diagonal action on a product of two G-sets (split into orbits later)."""
    pa, qa = A
    pb, qb = B
    na, nb = len(pa), len(pb)
    pts = [(x, y) for x in range(na) for y in range(nb)]
    perm = [[qa[i][x] * nb + qb[i][y] for (x, y) in pts] for i in range(5)]
    return pts, perm


def orbits_of(perm):
    n = len(perm[0])
    seen = [False] * n
    out = []
    for s in range(n):
        if seen[s]:
            continue
        comp = [s]
        seen[s] = True
        k = 0
        while k < len(comp):
            x = comp[k]
            k += 1
            for i in range(5):
                y = perm[i][x]
                if not seen[y]:
                    seen[y] = True
                    comp.append(y)
        idx = {x: j for j, x in enumerate(comp)}
        out.append([[idx[perm[i][x]] for x in comp] for i in range(5)])
    return out


def check(perm, relators):
    """Verify that every relator acts trivially (so X is a genuine Sp_4(Z)-set)."""
    n = len(perm[0])
    invp = [[0] * n for _ in range(5)]
    for i in range(5):
        for x in range(n):
            invp[i][perm[i][x]] = x
    for name, r in relators.items():
        for x in range(n):
            y = x
            for (i, e) in reversed(r):
                y = perm[i][y] if e > 0 else invp[i][y]
            assert y == x, (name, x)
    return invp
