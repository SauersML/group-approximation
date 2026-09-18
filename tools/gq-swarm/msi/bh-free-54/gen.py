#!/usr/bin/env python3
"""Rank-generic test of the reduction  Ore_atom <= SyncT + LD_atom*  for the edge-split operad (ranks n = 2, 3, 4).

For a random split tree U0 of Delta and an atom a = (i,j) with children c1 = {x_i >= x_j}, c2 = {x_j >= x_i}:
  1. resolve the plane x_i = x_j inside every crossing leaf (cut lemma, Euclid rule)            -> U1
  2. replace every leaf q of U1 on side S that is not in Desc(S) by a won synchronization tree   -> U
     (bh-free-61's game: left reductions of the S-side, braid-cut right splits of q)
  3. LD_atom* asks: is U|c1 a split tree of c1 and U|c2 one of c2?  (then U >=_E T and U >=_E E_a)
Also: LD_atom (no hypothesis) on U1, a planted positive (the 17-piece counterexample), and INT: if l descends
from cells A and B and A n B is a cell K, does l descend from K?  Calibration: rank 2, where all of this holds.
"""
import sys, json, time, random, itertools
sys.setrecursionlimit(100000)
T0 = time.time()
TL = 1e9
rnd = random.Random(20260918)


def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return sum((-1) ** c * M[0][c] * det([r[:c] + r[c + 1:] for r in M[1:]]) for c in range(n) if M[0][c])


def cols_to_mat(vs):
    n = len(vs)
    return [[vs[c][r] for c in range(n)] for r in range(n)]


INV = {}


def inv(C):
    if C in INV:
        return INV[C]
    F = cols_to_mat(C)
    n = len(F)
    d = det(F)
    assert abs(d) == 1, C
    A = [[0] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            minor = [row[:c] + row[c + 1:] for k, row in enumerate(F) if k != r]
            A[c][r] = (-1) ** (r + c) * det(minor) * d
    INV[C] = A
    return A


def mul(A, v):
    return tuple(sum(A[r][k] * v[k] for k in range(len(v))) for r in range(len(A)))


def cell(vs):
    return tuple(sorted(vs))


def inside(x, C):
    return all(y >= 0 for y in mul(inv(C), x))


def sub(p, C):
    return all(inside(v, C) for v in p)


def rel(p, C):
    """rows of the frame of p in C's coordinates"""
    A = inv(C)
    cs = [mul(A, v) for v in p]
    n = len(p)
    return tuple(tuple(cs[c][r] for c in range(n)) for r in range(n))


DM = {}


def desc(Y):
    key = tuple(sorted(Y))
    if key in DM:
        return DM[key]
    n = len(Y)
    if all(sum(r) == 1 and max(r) == 1 for r in Y):
        DM[key] = True
        return True
    res = False
    for a in range(n):
        for b in range(n):
            if a != b and all(Y[a][c] >= Y[b][c] for c in range(n)):
                Z = list(Y)
                Z[a] = tuple(Y[a][c] - Y[b][c] for c in range(n))
                if desc(tuple(Z)):
                    res = True
                    break
        if res:
            break
    DM[key] = res
    return res


def isdesc(p, C):
    return sub(p, C) and desc(rel(p, C))


def splits(C):
    out = []
    n = len(C)
    for i in range(n):
        for j in range(i + 1, n):
            u = tuple(C[i][k] + C[j][k] for k in range(len(C[i])))
            a = list(C)
            a[j] = u
            b = list(C)
            b[i] = u
            out.append((cell(a), cell(b)))
    return out


TM = {}


def is_tree(C, pieces):
    pieces = frozenset(pieces)
    if len(pieces) == 1:
        return next(iter(pieces)) == C
    key = (C, pieces)
    if key in TM:
        return TM[key]
    res = False
    for c1, c2 in splits(C):
        s1 = frozenset(p for p in pieces if sub(p, c1))
        s2 = frozenset(p for p in pieces if sub(p, c2))
        if s1 and s2 and len(s1) + len(s2) == len(pieces) and is_tree(c1, s1) and is_tree(c2, s2):
            res = True
            break
    TM[key] = res
    return res


def delta(n):
    return cell([tuple(1 if k == i else 0 for k in range(n)) for i in range(n)])


def rand_tree(C, k):
    L = [C]
    while len(L) < k:
        t = L.pop(rnd.randrange(len(L)))
        c1, c2 = rnd.choice(splits(t))
        L += [c1, c2]
    return L


def resolve(p, ell, d=0):
    a = [sum(ell[k] * v[k] for k in range(len(v))) for v in p]
    if not (min(a) < 0 < max(a)):
        return [p]
    if d > 400:
        raise RuntimeError("resolve")
    i = max(range(len(a)), key=lambda k: abs(a[k]))
    j = max((k for k in range(len(a)) if a[k] * a[i] < 0), key=lambda k: abs(a[k]))
    u = tuple(p[i][k] + p[j][k] for k in range(len(p[i])))
    x = list(p)
    x[j] = u
    y = list(p)
    y[i] = u
    return resolve(cell(x), ell, d + 1) + resolve(cell(y), ell, d + 1)


class Cap(Exception):
    pass


def sync_tree(q, S):
    """split tree of q (list of leaves) whose leaves all lie in Desc(S); braid-cut strategy."""
    n = len(q)
    Y0 = [list(r) for r in rel(q, S)]

    def rec(vs, Y, d):
        if d > 120:
            raise Cap
        Y = [r[:] for r in Y]
        while True:
            if all(sum(r) == 1 and max(r) == 1 for r in Y):
                return [cell(vs)]
            dom = None
            for a in range(n):
                for b in range(n):
                    if a != b and all(Y[a][c] >= Y[b][c] for c in range(n)):
                        Z = [r[:] for r in Y]
                        Z[a] = [Y[a][c] - Y[b][c] for c in range(n)]
                        if dom is None or desc(tuple(map(tuple, Z))):
                            dom = Z
                            if desc(tuple(map(tuple, Z))):
                                break
                if dom is not None and desc(tuple(map(tuple, dom))):
                    break
            if dom is None:
                break
            Y = dom
        best = None
        for a in range(n):
            for b in range(a + 1, n):
                w = [Y[a][c] - Y[b][c] for c in range(n)]
                if min(w) < 0 < max(w):
                    sc = max(abs(x) for x in w)
                    if best is None or sc < best[0]:
                        best = (sc, w)
        w = best[1]
        i = max(range(n), key=lambda k: abs(w[k]))
        j = max((k for k in range(n) if w[k] * w[i] < 0), key=lambda k: abs(w[k]))
        u = tuple(vs[i][k] + vs[j][k] for k in range(len(vs[i])))
        v1 = list(vs); v1[j] = u
        Y1 = [r[:] for r in Y]
        for r in Y1: r[j] = r[i] + r[j]
        v2 = list(vs); v2[i] = u
        Y2 = [r[:] for r in Y]
        for r in Y2: r[i] = r[i] + r[j]
        return rec(v1, Y1, d + 1) + rec(v2, Y2, d + 1)
    return rec(list(q), Y0, 0)


def pipeline(U0, C, i, j, n):
    ell = tuple((1 if k == i else -1 if k == j else 0) for k in range(n))
    c1 = [c for c in splits(C)[0:0]]
    kids = [s for s in splits(C) if all((v[i] - v[j]) >= 0 for v in s[0]) and all((v[j] - v[i]) >= 0 for v in s[1])]
    c1, c2 = kids[0]
    U1 = [x for p in U0 for x in resolve(p, ell)]
    ld_atom = is_tree(c1, [p for p in U1 if sub(p, c1)]) and is_tree(c2, [p for p in U1 if sub(p, c2)])
    U, nsync = [], 0
    for p in U1:
        S = c1 if sub(p, c1) else c2
        if isdesc(p, S):
            U.append(p)
        else:
            nsync += 1
            U += sync_tree(p, S)
    okU = is_tree(C, U)
    star = is_tree(c1, [p for p in U if sub(p, c1)]) and is_tree(c2, [p for p in U if sub(p, c2)])
    return {"ld_atom": ld_atom, "nsync": nsync, "U_is_tree": okU, "ld_atom_star": star, "size": len(U)}


