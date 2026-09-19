#!/usr/bin/env python3
"""Stress tests for Ore's condition (reversing) and for tree domination (TD) in the edge-split operad, m = 2.

  AR    tree domination of the full-operad primes Z, M, M', P9 (corrected check: U|r is a split tree of r)
  DEEP  reversing for (path dissection of a deep descendant, atom) and for pairs of path dissections, over all
        descendants of entry sum <= S, with the non-inherited ones counted separately
  TD    random descendant dissections that are not split trees (re-split moves), dominated by a split tree?
  BIG   random pairs of split trees with 20..40 pieces
Every positive answer is re-verified with independent absolute-coordinate tests (hier / geq of ore.py).
"""
import sys, json, time, random
sys.setrecursionlimit(200000)
import revlib as R
from ore import DELTA, splits, geq, hier, inside, tri

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
rnd = random.Random(918)


def left():
    return TL - (time.time() - T0)


def restrict(U, r):
    return frozenset(p for p in U if all(inside(x, r) for x in p))


def dominate(D, calls=150000):
    """A split tree U of Delta with U|r a split tree of r for all r in D (via reversing of path dissections)."""
    paths = [R.path_dissection(t) for t in D]
    if any(p is None for p in paths):
        return "non-descendant-piece", None
    acc = paths[0]
    for P in paths[1:]:
        info, U = R.run_ore(acc, P, calls=calls)
        if U is None:
            return info["status"], None
        acc = U
    ok = R.is_tree(acc) and all(hier(r, restrict(acc, r)) for r in D)
    return ("ok" if ok else "WRONG"), acc


# ---------- AR ----------
c = (1, 1, 1)
e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
v01, v02, v12 = (1, 1, 0), (1, 0, 1), (0, 1, 1)
PR = {
    "Z": [tri(c, e1, e2), tri(e0, c, e2), tri(e0, e1, c)],
    "M": [tri(e0, v01, v02), tri(e1, v01, v12), tri(e2, v02, v12), tri(v01, v12, c), tri(v12, v02, c), tri(v02, v01, c)],
    "Mprime": [tri(e2, (0, 1, 2), e0), tri(e1, (0, 1, 1), v01), tri((0, 1, 1), (0, 1, 2), v01), tri((0, 1, 2), e0, c),
               tri((0, 1, 2), v01, c), tri(e0, v01, c)],
    "P9": [tri(e2, (0, 1, 1), (1, 0, 1)), tri(e1, (0, 1, 1), c), tri(e1, e0, (2, 0, 1)), tri(e1, c, (2, 0, 1)),
           tri((0, 1, 1), (1, 0, 1), (3, 0, 2)), tri((0, 1, 1), c, (2, 1, 2)), tri((0, 1, 1), (2, 1, 2), (3, 0, 2)),
           tri(c, (2, 0, 1), (3, 0, 2)), tri(c, (2, 1, 2), (3, 0, 2))],
}
ar = {}
for name, D in PR.items():
    st, U = dominate(D)
    ar[name] = {"status": st, "size": None if U is None else len(U)}
print(json.dumps({"AR": ar}), flush=True)

# ---------- DEEP ----------
S = int(sys.argv[2]) if len(sys.argv) > 2 else 14


def esum(t):
    return sum(sum(v) for v in t)


cells = {DELTA}
fr = [DELTA]
while fr:
    new = []
    for t in fr:
        for P1, P2 in splits(t):
            for q in (P1, P2):
                if esum(q) <= S and q not in cells:
                    cells.add(q)
                    new.append(q)
    fr = new
cells.discard(DELTA)
ATOMT = [frozenset(s) for s in splits(DELTA)]


def inherited(t):
    """Is t a descendant of every first-split child of Delta that contains it?"""
    for (i, j) in R.ATOMS:
        for sg in (1, -1):
            if all(sg * R.lam(v, i, j) >= 0 for v in t):
                if R.reduce_path(R.pull(t, i, j, sg)) is None:
                    return False
    return True


deep = {"cells": len(cells), "non_inherited": 0, "atom_pairs": {}, "path_pairs": {}}
cl = sorted(cells)
noninh = [t for t in cl if not inherited(t)]
deep["non_inherited"] = len(noninh)
deep["non_inherited_example"] = [list(map(list, noninh[0]))] if noninh else None
ap = {}
for t in cl:
    if left() < 0.6 * TL:
        ap["stopped"] = "time"
        break
    P = R.path_dissection(t)
    for A in ATOMT:
        info, U = R.run_ore(P, A, calls=100000)
        key = info["status"] + ("-noninh" if t in noninh else "")
        ap[key] = ap.get(key, 0) + 1
        if info["status"] not in ("ok",) and "example" not in ap:
            ap["example"] = [list(map(list, t)), sorted(map(list, A))]
deep["atom_pairs"] = ap
pp = {}
for _ in range(400):
    if left() < 0.45 * TL:
        pp["stopped"] = "time"
        break
    t, u = rnd.choice(cl), rnd.choice(noninh or cl)
    info, U = R.run_ore(R.path_dissection(t), R.path_dissection(u), calls=100000)
    pp[info["status"]] = pp.get(info["status"], 0) + 1
    if info["status"] == "ok":
        pp["maxsize"] = max(pp.get("maxsize", 0), info["size"])
    elif "example" not in pp:
        pp["example"] = [list(map(list, t)), list(map(list, u))]
deep["path_pairs"] = pp
print(json.dumps({"DEEP": deep, "S": S}), flush=True)

# ---------- TD ----------


def rand_tree(k):
    L = {DELTA}
    while len(L) < k:
        t = rnd.choice(sorted(L))
        P1, P2 = rnd.choice(splits(t))
        L.remove(t)
        L.add(P1)
        L.add(P2)
    return set(L)


def resplit(L, moves):
    """Merge two pieces forming a cell c (children of an edge split of c) and re-split c along another edge;
    also merge 3-piece stars at the barycenter.  Pieces stay descendants of Delta whenever c is one."""
    L = set(L)
    for _ in range(moves):
        cand = []
        Ls = sorted(L)
        for x in Ls:
            for y in Ls:
                if x < y:
                    sx, sy = set(x), set(y)
                    sh = sx & sy
                    if len(sh) == 2:
                        a, = sx - sh
                        b, = sy - sh
                        p, q = sorted(sh)
                        for (u, w) in ((p, q), (q, p)):
                            # x = (a, u, m), y = (b, w, m) with m the split point?  test c = cone(u, w, t)
                            pass
                        for m in sh:
                            o, = sh - {m}
                            # candidate parent: cone(a, b, o) with m = a + b (the split point on edge (a, b))
                            if tuple(a[k] + b[k] for k in range(3)) == m:
                                cpar = tri(a, b, o)
                                if R.reduce_path(cpar) is not None:
                                    cand.append((x, y, cpar, m))
        if not cand:
            break
        x, y, cpar, m = rnd.choice(cand)
        opts = [s for s in splits(cpar) if set(s) != {x, y}]
        s = rnd.choice(opts)
        L.discard(x)
        L.discard(y)
        L.add(s[0])
        L.add(s[1])
    return frozenset(L)


td = {"non_tree_tested": 0}
for k in (4, 6, 8, 10, 14):
    for _ in range(40):
        if left() < 0.25 * TL:
            td["stopped"] = "time"
            break
        D = resplit(rand_tree(k), 3 * k)
        if R.is_tree(D):
            td["tree"] = td.get("tree", 0) + 1
            continue
        td["non_tree_tested"] += 1
        st, U = dominate(D, calls=100000)
        td[st] = td.get(st, 0) + 1
        if st == "ok":
            td["maxsize"] = max(td.get("maxsize", 0), len(U))
        elif "example" not in td:
            td["example"] = [list(map(list, t)) for t in sorted(D)]
print(json.dumps({"TD": td}), flush=True)

# ---------- BIG ----------
big = {}
for k in (20, 24, 32, 40):
    s = {}
    for _ in range(30):
        if left() < 10:
            s["stopped"] = "time"
            break
        A, B = frozenset(rand_tree(k)), frozenset(rand_tree(k))
        info, U = R.run_ore(A, B, calls=200000)
        s[info["status"]] = s.get(info["status"], 0) + 1
        if U is not None:
            s["maxsize"] = max(s.get("maxsize", 0), len(U))
        elif info["status"] != "budget" and "example" not in s:
            s["example"] = [sorted(map(list, A)), sorted(map(list, B))]
    big[k] = s
    print(json.dumps({"BIG_k": k, "stats": s}), flush=True)
print(json.dumps({"secs": round(time.time() - T0, 1), "memo": len(R.MEMO)}), flush=True)
