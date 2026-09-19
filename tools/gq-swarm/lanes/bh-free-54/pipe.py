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
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 540.0
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


out = {}
# planted positive (rank 3): the 17-piece counterexample to LD_atom
Dp = [((0,0,1),(0,1,0),(1,1,1)),((0,0,1),(1,0,1),(1,1,1)),((0,1,0),(1,1,0),(3,3,1)),((0,1,0),(1,1,1),(2,2,1)),((0,1,0),(2,2,1),(3,3,1)),((1,0,0),(1,1,0),(3,2,1)),((1,0,0),(3,0,1),(3,1,1)),((1,0,0),(3,1,1),(3,2,1)),((1,0,1),(1,1,1),(2,1,1)),((1,0,1),(2,0,1),(2,1,1)),((1,1,0),(3,2,1),(3,3,1)),((1,1,1),(2,1,1),(2,2,1)),((2,0,1),(2,1,1),(3,0,1)),((2,1,1),(2,2,1),(3,0,1)),((2,2,1),(3,0,1),(3,1,1)),((2,2,1),(3,1,1),(3,2,1)),((2,2,1),(3,2,1),(3,3,1))]
Dp = [cell(t) for t in Dp]
out["planted_rank3"] = pipeline(Dp, delta(3), 0, 1, 3)
print(json.dumps({"planted": out["planted_rank3"]}), flush=True)


def run_pipeline(n, ks, per, frac):
    C = delta(n)
    st = {"instances": 0, "trivial_first_split": 0, "ld_atom_fail": 0, "sync_needed": 0, "U_not_tree": 0,
          "ld_atom_star_fail": 0, "cap": 0, "maxsize": 0}
    for k in ks:
        for _ in range(per):
            if time.time() - T0 > frac * TL:
                st["stopped"] = "time"
                return st
            U0 = rand_tree(C, k)
            for i in range(n):
                for j in range(i + 1, n):
                    st["instances"] += 1
                    try:
                        r = pipeline(U0, C, i, j, n)
                    except (Cap, RuntimeError, RecursionError):
                        st["cap"] += 1
                        continue
                    st["ld_atom_fail"] += (not r["ld_atom"])
                    st["sync_needed"] += (r["nsync"] > 0)
                    st["U_not_tree"] += (not r["U_is_tree"])
                    st["maxsize"] = max(st["maxsize"], r["size"])
                    if not r["ld_atom_star"]:
                        st["ld_atom_star_fail"] += 1
                        if "example" not in st:
                            st["example"] = {"U0": U0, "atom": [i, j]}
    return st


out["calib_rank2"] = run_pipeline(2, (2, 4, 8, 16, 32), 30, 0.05)
print(json.dumps({"calib_rank2": out["calib_rank2"]}), flush=True)
out["rank3"] = run_pipeline(3, (4, 8, 12, 16, 24, 32), 60, 0.40)
print(json.dumps({"rank3": out["rank3"]}), flush=True)
out["rank4"] = run_pipeline(4, (4, 6, 8, 10, 12), 40, 0.65)
print(json.dumps({"rank4": out["rank4"]}), flush=True)


# INT: l in Desc(A) n Desc(B), A n B = K a cell  =>  l in Desc(K)?
def nullvec(rows, n):
    v = []
    for c in range(n):
        minor = [r[:c] + r[c + 1:] for r in rows]
        v.append((-1) ** c * det(minor))
    return v


def meet_cell(A, B, n):
    N = [list(r) for r in inv(A)] + [list(r) for r in inv(B)]
    rays = set()
    for sub_ in itertools.combinations(range(len(N)), n - 1):
        v = nullvec([N[s] for s in sub_], n)
        if not any(v):
            continue
        g = 0
        for x in v:
            g = abs(x) if g == 0 else __import__("math").gcd(g, abs(x))
        v = [x // g for x in v]
        for s in (1, -1):
            w = tuple(s * x for x in v)
            if all(sum(r[k] * w[k] for k in range(n)) >= 0 for r in N):
                rays.add(w)
    if len(rays) != n:
        return None
    K = cell(list(rays))
    return K if abs(det(cols_to_mat(K))) == 1 else None


def esum(t):
    return sum(sum(v) for v in t)


def int_test(n, S1, S2, frac):
    C = delta(n)
    cells = {C}
    fr = [C]
    while fr:
        new = []
        for t in fr:
            for c1, c2 in splits(t):
                for q in (c1, c2):
                    if esum(q) <= S1 and q not in cells:
                        cells.add(q)
                        new.append(q)
        fr = new
    small = [c for c in cells if esum(c) <= S2]
    st = {"n": n, "cells": len(cells), "small": len(small), "tested": 0, "violations": 0}
    MC = {}
    for l in sorted(cells):
        if time.time() - T0 > frac * TL:
            st["stopped"] = "time"
            break
        anc = [A for A in small if A != l and isdesc(l, A)]
        for A, B in itertools.combinations(anc, 2):
            if sub(A, B) or sub(B, A):
                continue
            key = (A, B)
            if key not in MC:
                MC[key] = meet_cell(A, B, n)
            K = MC[key]
            if K is None:
                continue
            st["tested"] += 1
            if not isdesc(l, K):
                st["violations"] += 1
                if "example" not in st:
                    st["example"] = {"l": l, "A": A, "B": B, "K": K}
    return st


out["int3"] = int_test(3, 13, 8, 0.85)
print(json.dumps({"INT3": out["int3"]}), flush=True)
out["int4"] = int_test(4, 9, 6, 0.97)
print(json.dumps({"INT4": out["int4"]}), flush=True)
print(json.dumps({"secs": round(time.time() - T0, 1)}), flush=True)
