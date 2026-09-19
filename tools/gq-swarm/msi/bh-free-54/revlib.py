#!/usr/bin/env python3
"""Reversing search for Ore's condition in the edge-split operad O_E on Delta = cone(e0,e1,e2) (m = 2).

All recursion is done in normalized coordinates: a half {x_i >= x_j} of Delta is pulled back to Delta by
v -> v - v_j e_i, the other half by v -> v - v_i e_j.  Dissections are frozensets of cells, a cell is a sorted
triple of primitive vectors.  ore(L1, L2) returns an O_E-dissection L >=_E L1, L2, or None (reversing failed for
every local choice), or raises Budget.  Results are re-verified with the independent absolute-coordinate test
geq() of ore.py.

Sections:  CE   the explicit counterexample to LD_atom (17 pieces) and its checks
           W    reversing on the witness pairs (E_01, D_e) and (E_01, D')
           AR   assembly of descendant dissections (Z, M, M', the 9-piece prime)
           RND  random pairs of O_E-dissections
"""
import sys, json, time, random, itertools
sys.setrecursionlimit(200000)
from ore import DELTA, splits, geq, hier, inside, det, tri

T0 = time.time()
TLIM = 1e9
ATOMS = ((0, 1), (0, 2), (1, 2))
PERMS = list(itertools.permutations(range(3)))


def lam(v, i, j):
    return v[i] - v[j]


def respects(L, i, j):
    for t in L:
        s = [lam(v, i, j) for v in t]
        if min(s) < 0 < max(s):
            return False
    return True


def side(t, i, j):
    return 1 if min(lam(v, i, j) for v in t) >= 0 else -1


def pull(t, i, j, sg):
    out = []
    for v in t:
        w = list(v)
        if sg > 0:
            w[i] -= w[j]
        else:
            w[j] -= w[i]
        out.append(tuple(w))
    return tri(*out)


def push(t, i, j, sg):
    out = []
    for v in t:
        w = list(v)
        if sg > 0:
            w[i] += w[j]
        else:
            w[j] += w[i]
        out.append(tuple(w))
    return tri(*out)


def halves(L, i, j):
    P = frozenset(pull(t, i, j, 1) for t in L if side(t, i, j) > 0)
    M = frozenset(pull(t, i, j, -1) for t in L if side(t, i, j) < 0)
    return P, M


def combine(i, j, P, M):
    return frozenset([push(t, i, j, 1) for t in P] + [push(t, i, j, -1) for t in M])


def permcell(t, p):
    return tri(*[tuple(v[p[k]] for k in range(3)) for v in t])


def permL(L, p):
    return frozenset(permcell(t, p) for t in L)


def invp(p):
    q = [0, 0, 0]
    for k in range(3):
        q[p[k]] = k
    return tuple(q)


def canon(L):
    best = None
    for p in PERMS:
        k = tuple(sorted(permcell(t, p) for t in L))
        if best is None or k < best[0]:
            best = (k, p)
    return best


def canon2(L1, L2):
    best = None
    for p in PERMS:
        k = (tuple(sorted(permcell(t, p) for t in L1)), tuple(sorted(permcell(t, p) for t in L2)))
        if best is None or k < best[0]:
            best = (k, p)
    return best


TREE = {}


def is_tree(L):
    if len(L) == 1:
        return next(iter(L)) == DELTA
    k = canon(L)[0]
    if k in TREE:
        return TREE[k]
    r = False
    for (i, j) in ATOMS:
        if respects(L, i, j):
            P, M = halves(L, i, j)
            if P and M and is_tree(P) and is_tree(M):
                r = True
                break
    TREE[k] = r
    return r


def first_splits(L):
    out = []
    if len(L) == 1:
        return out
    for (i, j) in ATOMS:
        if respects(L, i, j):
            P, M = halves(L, i, j)
            if P and M and is_tree(P) and is_tree(M):
                out.append((i, j))
    return out


def up_trees(N):
    seen = {frozenset([DELTA])}
    fr = [frozenset([DELTA])]
    while fr:
        new = []
        for X in fr:
            if len(X) >= N:
                continue
            for t in X:
                for P1, P2 in splits(t):
                    G = frozenset((X - {t}) | {P1, P2})
                    if G not in seen:
                        seen.add(G)
                        new.append(G)
        fr = new
    return seen


SMALL = up_trees(5)
MB = {}
for a in ATOMS:
    for b in ATOMS:
        if a == b:
            continue
        c = [X for X in SMALL if a in first_splits(X) and b in first_splits(X)]
        m = min(len(X) for X in c)
        MB[(a, b)] = sorted([X for X in c if len(X) == m], key=lambda X: sorted(X))


class Budget(Exception):
    pass


MEMO = {}
ST = {"calls": 0, "maxdepth": 0}
CAP = {"calls": 10 ** 6, "depth": 400, "size": 400}


def ore(L1, L2, depth=0):
    ST["calls"] += 1
    ST["maxdepth"] = max(ST["maxdepth"], depth)
    if ST["calls"] > CAP["calls"] or depth > CAP["depth"] or time.time() - T0 > TLIM:
        raise Budget
    if len(L1) == 1:
        return L2
    if len(L2) == 1 or L1 == L2:
        return L1
    (k, p) = canon2(L1, L2)
    if k in MEMO:
        R = MEMO[k]
        return None if R is None else permL(R, invp(p))
    F1, F2 = first_splits(L1), first_splits(L2)
    res = None
    common = [a for a in F1 if a in F2]
    for (i, j) in common:
        P1, M1 = halves(L1, i, j)
        P2, M2 = halves(L2, i, j)
        A = ore(P1, P2, depth + 1)
        if A is None:
            continue
        B = ore(M1, M2, depth + 1)
        if B is None:
            continue
        res = combine(i, j, A, B)
        break
    if res is None and not common:
        for a in F1:
            for b in F2:
                for R in MB[(a, b)]:
                    X = ore(L1, R, depth + 1)
                    if X is None:
                        continue
                    if len(X) > CAP["size"]:
                        raise Budget
                    Y = ore(X, L2, depth + 1)
                    if Y is not None:
                        res = Y
                        break
                if res is not None:
                    break
            if res is not None:
                break
    if res is not None and len(res) > CAP["size"]:
        raise Budget
    MEMO[k] = None if res is None else permL(res, p)
    return res


def run_ore(L1, L2, calls=200000):
    ST["calls"] = 0
    ST["maxdepth"] = 0
    CAP["calls"] = calls
    try:
        R = ore(L1, L2)
    except Budget:
        return {"status": "budget", "calls": ST["calls"], "maxdepth": ST["maxdepth"]}, None
    except RecursionError:
        return {"status": "recursion"}, None
    if R is None:
        return {"status": "reversing-failed", "calls": ST["calls"]}, None
    ok = is_tree(R) and geq(R, L1) and geq(R, L2)
    return {"status": "ok" if ok else "WRONG", "size": len(R), "calls": ST["calls"], "maxdepth": ST["maxdepth"]}, R


# ---------- descendant paths (row reduction) ----------
def rows(t):
    return [tuple(v[k] for v in t) for k in range(3)]


def reduce_path(t, memo=None):
    """A sequence of left reductions (a,b) taking the frame of t to a permutation, or None."""
    if memo is None:
        memo = {}
    X = [list(r) for r in rows(t)]
    key = tuple(map(tuple, X))

    def rec(X):
        key = tuple(map(tuple, X))
        if key in memo:
            return memo[key]
        if all(sorted(r) == [0, 0, 1] for r in X) and sorted(map(tuple, X)) == sorted([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            memo[key] = []
            return []
        memo[key] = None
        for a in range(3):
            for b in range(3):
                if a != b and all(X[a][c] >= X[b][c] for c in range(3)):
                    Y = [r[:] for r in X]
                    Y[a] = [X[a][c] - X[b][c] for c in range(3)]
                    s = rec(Y)
                    if s is not None:
                        memo[key] = [(a, b)] + s
                        return memo[key]
        return None
    return rec(X)


def path_dissection(t):
    s = reduce_path(t)
    if s is None:
        return None
    Y = [list(E) for E in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]   # columns
    sib = []
    for (a, b) in s:
        ch = [c[:] for c in Y]
        ch[b] = [Y[b][k] + Y[a][k] for k in range(3)]
        sb = [c[:] for c in Y]
        sb[a] = [Y[a][k] + Y[b][k] for k in range(3)]
        sib.append(tri(*map(tuple, sb)))
        Y = ch
    last = tri(*map(tuple, Y))
    assert last == t, (last, t)
    return frozenset(sib + [last])


def resolve(t, i, j, d=0):
    """Greedy edge-split resolution of the plane x_i = x_j inside the cell t (split a crossed edge)."""
    if d > 300:
        raise RuntimeError("resolve depth")
    s = [lam(v, i, j) for v in t]
    if not (min(s) < 0 < max(s)):
        return [t]
    a, b, c = t
    best = None
    for (p, q, r) in ((a, b, c), (a, c, b), (b, c, a)):
        lp, lq = lam(p, i, j), lam(q, i, j)
        if lp * lq < 0:
            sc = abs(lp) + abs(lq)
            if best is None or sc > best[0]:
                best = (sc, p, q, r)
    _, p, q, r = best
    u = (p[0] + q[0], p[1] + q[1], p[2] + q[2])
    return resolve(tri(p, u, r), i, j, d + 1) + resolve(tri(u, q, r), i, j, d + 1)


