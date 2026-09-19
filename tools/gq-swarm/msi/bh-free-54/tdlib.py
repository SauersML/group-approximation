#!/usr/bin/env python3
"""Tree domination by top-down cut-and-synchronize, ranks n = 2 (calibration), 3, 4.

td(C, D): at node C pick a first split of C (rule R1 'follow the deepest fragment along one descent step',
or R2 'least damage'); cut every fragment that straddles its plane (cut lemma), replace every fragment
that lies in a child without descending from it by a synchronization tree (bh-free-61's braid-cut game);
recurse.  The fragments of each piece r of D stay a split tree of r by construction, so on termination the
leaves T satisfy T in Trees(C) and T|r in Trees(r): both are re-verified independently (is_tree).
Instances: the four full-operad primes; bh-major-mcg-2's 10-piece restriction (227db96ee); restrictions
D = U|c of cut-and-synchronized random split trees to a first-split child c (the TD instances that the
Ore-atom reduction produces), kept only when D is not already a split tree of c.
"""
import sys, json, time, random
from fractions import Fraction
sys.setrecursionlimit(100000)
import gen as G
from gen import cell, sub, rel, isdesc, desc, inv, resolve, sync_tree, is_tree, delta, rand_tree, splits, Cap

T0 = time.time()
TL = 1e9
rnd = random.Random(918)
G.rnd.seed(918)


def esum(Y):
    return sum(sum(r) for r in Y)


def weight(p, C):
    Y = rel(p, C)
    w = Fraction(1)
    for c in range(len(Y)):
        w /= sum(Y[r][c] for r in range(len(Y)))
    return w


def children(C, i, j):
    u = tuple(C[i][k] + C[j][k] for k in range(len(C[i])))
    a = list(C); a[j] = u
    b = list(C); b[i] = u
    return cell(a), cell(b)          # {y_i >= y_j}, {y_j >= y_i}


def first_step(f, C):
    Y = rel(f, C)
    n = len(Y)
    for a in range(n):
        for b in range(n):
            if a != b and all(Y[a][c] >= Y[b][c] for c in range(n)):
                Z = list(Y)
                Z[a] = tuple(Y[a][c] - Y[b][c] for c in range(n))
                if desc(tuple(Z)):
                    return (min(a, b), max(a, b))
    return None


def damage(C, frags, i, j):
    c1, c2 = children(C, i, j)
    d = 0
    for f in frags:
        if sub(f, c1):
            d += 0 if isdesc(f, c1) else 1
        elif sub(f, c2):
            d += 0 if isdesc(f, c2) else 1
        else:
            d += 2
    return d


def choose(C, frags, rule):
    deepest = max(frags, key=lambda f: (esum(rel(f, C)), f))
    fs = first_step(deepest, C)
    if rule == "R1":
        return fs
    n = len(C)
    best = None
    for i in range(n):
        for j in range(i + 1, n):
            key = (damage(C, frags, i, j), 0 if (i, j) == fs else 1)
            if best is None or key < best[0]:
                best = (key, (i, j))
    return best[1]


def td(C, frags, rule, st, depth=0):
    st["maxdepth"] = max(st["maxdepth"], depth)
    if depth > 250 or st["leaves"] > 6000 or time.time() - T0 > TL:
        raise Cap
    if len(frags) == 1:
        assert frags[0] == C
        st["leaves"] += 1
        return [C]
    i, j = choose(C, frags, rule)
    c1, c2 = children(C, i, j)
    A = inv(C)
    ell = tuple(A[i][k] - A[j][k] for k in range(len(C)))
    L1, L2 = [], []
    for f in frags:
        if sub(f, c1):
            L1.append(f)
        elif sub(f, c2):
            L2.append(f)
        else:
            st["cuts"] += 1
            for g in resolve(f, ell):
                (L1 if sub(g, c1) else L2).append(g)
    out = []
    for ch, L in ((c1, L1), (c2, L2)):
        M = []
        for f in L:
            if isdesc(f, ch):
                M.append(f)
            else:
                st["syncs"] += 1
                leaves = sync_tree(f, ch)
                assert all(isdesc(x, ch) for x in leaves)
                M += leaves
        out += td(ch, M, rule, st, depth + 1)
    return out


def run(C, D, rule):
    st = {"maxdepth": 0, "leaves": 0, "cuts": 0, "syncs": 0}
    try:
        T = td(C, list(D), rule, st)
    except (Cap, RuntimeError, RecursionError):
        return "cap", st, None
    ok = is_tree(C, T) and all(is_tree(r, [t for t in T if sub(t, r)]) for r in D)
    return ("ok" if ok else "WRONG"), st, T


def agg(stats, status, st, T, D):
    stats[status] = stats.get(status, 0) + 1
    for k in ("maxdepth", "cuts", "syncs"):
        stats["max_" + k] = max(stats.get("max_" + k, 0), st[k])
    if T is not None:
        stats["max_leaves"] = max(stats.get("max_leaves", 0), len(T))
        stats["max_ratio"] = max(stats.get("max_ratio", 0), round(len(T) / len(D), 2))


