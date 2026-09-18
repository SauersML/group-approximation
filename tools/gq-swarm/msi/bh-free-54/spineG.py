#!/usr/bin/env python3
"""Spine of the rank-3 edge-split operad and Thumann splitting categories A(Theta) (condition (G)).

Spine: start from the three atoms; repeatedly add the minimal common upper bounds (in >=_E) of pairs of spine
elements.  ub_min(A, B, N) is exact up to N pieces: it enumerates refinements X of the larger element by edge
splits, pruning X when its leaves crossing a wall of the other element outnumber the splits left, and stops
at the first X >=_E both (refinements of a bound are never minimal); branching is only over the splits of one
wall-crossing leaf, or over the leaves inside a piece of the other element whose restriction is not yet a split
tree, which loses no bound.  Pairs with no bound of at most N pieces are counted as truncated.
A(Theta) (bh-invent-07 / bh-major-mcg-2): split trees D' with Delta < D' <_E Theta such that on every piece p
of D', Theta|p (pulled back to Delta) is trivial or a spine element.  Ordered by coarsening; we report the
number of elements and connected components.  Calibration: the 5-piece flop elements have 6 elements in 2
components (edge-split-flop-spine-elements-split-disconnectedly).
"""
import sys, json, time, itertools
from ore import DELTA, splits, geq, hier, inside, det, tri

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
PERMS = list(itertools.permutations(range(3)))


def canon(D):
    return min(tuple(sorted(tri(*[tuple(v[p[k]] for k in range(3)) for v in t]) for t in D)) for p in PERMS)


def in_one(p, B):
    return any(all(inside(x, q) for x in p) for q in B)


def ub_min(A, B, N):
    if len(B) > len(A):
        A, B = B, A
    seen, sols = set(), []
    stack = [A]
    while stack:
        if time.time() - T0 > TL:
            raise TimeoutError
        X = stack.pop()
        if X in seen:
            continue
        seen.add(X)
        bad = sorted(p for p in X if not in_one(p, B))
        if len(X) + len(bad) > N or (len(X) >= N and bad):
            continue
        if bad:
            cand = [bad[0]]              # every bound splits this leaf; the split order of leaves is irrelevant
        else:
            cand = []
            for q in B:
                inq = frozenset(p for p in X if all(inside(x, q) for x in p))
                if not hier(q, inq):
                    cand += sorted(inq)   # some leaf inside a failing piece must be split
            if not cand:
                sols.append(X)
                continue
            if len(X) >= N:
                continue
        for p in cand:
            for P1, P2 in splits(p):
                stack.append(frozenset((X - {p}) | {P1, P2}))
    sols.sort(key=len)
    mins = [S for i, S in enumerate(sols) if not any(len(T) < len(S) and geq(S, T) for T in sols[:i])]
    return mins, len(seen)


def pullback(p, cells):
    a, b, c = p
    d = det(a, b, c)
    cols = (a, b, c)
    # inverse of the frame with columns a, b, c (det = +-1)
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    adj = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m = [[M[r][s] for s in range(3) if s != j] for r in range(3) if r != i]
            adj[j][i] = (-1) ** (i + j) * (m[0][0] * m[1][1] - m[0][1] * m[1][0]) * d
    return frozenset(tri(*[tuple(sum(adj[r][k] * v[k] for k in range(3)) for r in range(3)) for v in q]) for q in cells)


def restrict(Th, p):
    return frozenset(q for q in Th if all(inside(x, p) for x in q))


def prefixes(c, Tc, memo):
    key = (c, Tc)
    if key in memo:
        return memo[key]
    res = {frozenset([c])}
    if len(Tc) > 1:
        for P1, P2 in splits(c):
            s1 = frozenset(q for q in Tc if all(inside(x, P1) for x in q))
            s2 = frozenset(q for q in Tc if all(inside(x, P2) for x in q))
            if s1 and s2 and len(s1) + len(s2) == len(Tc) and hier(P1, s1) and hier(P2, s2):
                for W1 in prefixes(P1, s1, memo):
                    for W2 in prefixes(P2, s2, memo):
                        res.add(W1 | W2)
    memo[key] = res
    return res


def splitting_category(Th, spine_canon):
    W_all = prefixes(DELTA, Th, {})
    elems = []
    for W in W_all:
        if len(W) == 1 or W == Th:
            continue
        ok = True
        for p in W:
            r = restrict(Th, p)
            if len(r) > 1 and canon(pullback(p, r)) not in spine_canon:
                ok = False
                break
        if ok:
            elems.append(W)
    parent = list(range(len(elems)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in range(len(elems)):
        for j in range(i + 1, len(elems)):
            a, b = elems[i], elems[j]
            if (len(a) < len(b) and geq(b, a)) or (len(b) < len(a) and geq(a, b)):
                parent[find(i)] = find(j)
    comps = len({find(i) for i in range(len(elems))})
    return len(elems), comps, sorted(len(W) for W in elems)


atoms = [frozenset(s) for s in splits(DELTA)]
spine = {canon(a): a for a in atoms}
rounds = []
cur_new = list(atoms)
stopped = None
for r in range(1, 6):
    new = {}
    trunc = 0
    elems = list(spine.values())
    try:
        for A in cur_new:
            for B in elems:
                if A == B:
                    continue
                if (len(A) < len(B) and geq(B, A)) or (len(B) < len(A) and geq(A, B)):
                    continue
                mins, _ = ub_min(A, B, N)
                if not mins:
                    trunc += 1
                for S in mins:
                    k = canon(S)
                    if k not in spine and k not in new:
                        new[k] = S
    except TimeoutError:
        stopped = "time in round %d" % r
    by = {}
    for S in new.values():
        by[len(S)] = by.get(len(S), 0) + 1
    rounds.append({"round": r, "new_up_to_S3": len(new), "by_size": dict(sorted(by.items())), "truncated": trunc})
    print(json.dumps(rounds[-1]), flush=True)
    spine.update(new)
    # every S3 image is a spine element too
    cur_new = []
    for S in new.values():
        for p in PERMS:
            cur_new.append(frozenset(tri(*[tuple(v[p[k]] for k in range(3)) for v in t]) for t in S))
    cur_new = list(set(cur_new))
    if stopped or not new:
        break
print(json.dumps({"spine_up_to_S3_by_size": dict(sorted({len(S): sum(1 for T in spine.values() if len(T) == len(S)) for S in spine.values()}.items())),
                  "N": N, "stopped": stopped, "secs": round(time.time() - T0, 1)}), flush=True)

spine_canon = set(spine.keys())
res = []
for k, Th in sorted(spine.items(), key=lambda kv: len(kv[1])):
    if len(Th) < 3:
        continue
    if time.time() - T0 > TL + 60:
        res.append({"stopped": "time"})
        break
    n_el, comps, sizes = splitting_category(Th, spine_canon)
    res.append({"size": len(Th), "A_elements": n_el, "components": comps, "element_sizes": sizes})
    print(json.dumps(res[-1]), flush=True)
print(json.dumps({"done": True, "secs": round(time.time() - T0, 1)}), flush=True)
