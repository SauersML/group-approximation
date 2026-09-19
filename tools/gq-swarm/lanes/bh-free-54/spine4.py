#!/usr/bin/env python3
"""Rank-generic exact spine closure for the edge-split operad (spineG.py's method on gen.py): rank 3 (calibration:
must reproduce 8 classes of sizes 2,5,5,6,7,8,10,12 at N = 12) and rank 4 (the next case for the closed-MCG host).
geq(X, B): X refines B and X|q is a split tree of q for every piece q of B."""
import sys, json, time, itertools
sys.setrecursionlimit(100000)
from gen import cell, sub, splits, is_tree, delta

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 200.0


def geq(X, B):
    for q in B:
        inq = frozenset(p for p in X if sub(p, q))
        if not inq or not is_tree(q, inq):
            return False
    return sum(1 for p in X if any(sub(p, q) for q in B)) == len(X)


def canon(D, n):
    return min(tuple(sorted(cell([tuple(v[p[k]] for k in range(n)) for v in t]) for t in D))
               for p in itertools.permutations(range(n)))


def images(D, n):
    return {frozenset(cell([tuple(v[p[k]] for k in range(n)) for v in t]) for t in D) for p in itertools.permutations(range(n))}


def ub_min(A, B, N, tl):
    if len(B) > len(A):
        A, B = B, A
    seen, sols, stack = set(), [], [A]
    while stack:
        if time.time() - T0 > tl:
            raise TimeoutError
        X = stack.pop()
        if X in seen:
            continue
        seen.add(X)
        bad = sorted(p for p in X if not any(sub(p, q) for q in B))
        if len(X) + len(bad) > N or (len(X) >= N and bad):
            continue
        if bad:
            cand = [bad[0]]
        else:
            cand = []
            for q in B:
                inq = frozenset(p for p in X if sub(p, q))
                if not is_tree(q, inq):
                    cand += sorted(inq)
            if not cand:
                sols.append(X)
                continue
            if len(X) >= N:
                continue
        for p in cand:
            for P1, P2 in splits(p):
                stack.append(frozenset((X - {p}) | {P1, P2}))
    sols.sort(key=len)
    return [S for i, S in enumerate(sols) if not any(len(T) < len(S) and geq(S, T) for T in sols[:i])]


def closure(n, N, tl):
    atoms = [frozenset(s) for s in splits(delta(n))]
    spine = {}
    for a in atoms:
        spine.setdefault(canon(a, n), a)
    cur = list(atoms)
    rounds = []
    for r in range(1, 8):
        new, trunc = {}, 0
        elems = list(spine.values())
        try:
            for A in cur:
                for B in elems:
                    if A == B or (len(A) < len(B) and geq(B, A)) or (len(B) < len(A) and geq(A, B)):
                        continue
                    mins = ub_min(A, B, N, tl)
                    trunc += (not mins)
                    for S in mins:
                        k = canon(S, n)
                        if k not in spine and k not in new:
                            new[k] = S
        except TimeoutError:
            rounds.append({"round": r, "stopped": "time", "new_so_far": len(new)})
            return spine, rounds, False
        by = {}
        for S in new.values():
            by[len(S)] = by.get(len(S), 0) + 1
        rounds.append({"round": r, "new_up_to_Sn": len(new), "by_size": dict(sorted(by.items())), "truncated": trunc})
        spine.update(new)
        cur = [I for S in new.values() for I in images(S, n)]
        if not new:
            return spine, rounds, trunc == 0
    return spine, rounds, False


for n, N, frac in ((3, 12, 0.25), (4, 10, 0.6), (4, 12, 1.0)):
    t = time.time()
    try:
        spine, rounds, closed = closure(n, N, frac * TL)
    except RecursionError:
        print(json.dumps({"rank": n, "N": N, "error": "recursion"}), flush=True)
        continue
    sizes = sorted(len(S) for S in spine.values())
    print(json.dumps({"rank": n, "N": N, "classes": len(spine), "sizes": sizes, "rounds": rounds,
                      "closed_without_truncation": closed, "secs": round(time.time() - t, 1)}), flush=True)
