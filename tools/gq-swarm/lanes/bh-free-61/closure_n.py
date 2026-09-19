#!/usr/bin/env python3
# bh-free-61: complement closure (C) for the edge-split operad in rank n (cones in R^n, m = n - 1).
# Same algorithm as closure.py (rank 3), written for general n with exact integer inverses.
# (C): S contains the atoms, is invariant under coordinate permutations, and for all A, B in S there is a
# common >=_E upper bound U with every restriction U|l (l a leaf of A or of B, in l's frame) in S or trivial.
# (C) implies Ore for O_E by the Garside grid (see the node). Greedy build; stops when a pass adds nothing.
import sys, json, time, itertools
from fractions import Fraction
from functools import lru_cache

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
N = int(sys.argv[2]) if len(sys.argv) > 2 else 12
MAXPASS = int(sys.argv[3]) if len(sys.argv) > 3 else 8
LEVEL_CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 300000
E = [tuple(1 if i == j else 0 for i in range(n)) for j in range(n)]

def add(u, v): return tuple(a + b for a, b in zip(u, v))
def cell(*cols): return tuple(sorted(cols))
DELTA = cell(*E)

@lru_cache(maxsize=None)
def inv(K):
    # K: tuple of n column vectors; return integer inverse rows (K unimodular)
    M = [[Fraction(K[c][r]) for c in range(n)] + [Fraction(1 if r == i else 0) for i in range(n)] for r in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    rows = tuple(tuple(int(x) for x in M[r][n:]) for r in range(n))
    return rows

def coords(K, v):
    return tuple(sum(a * b for a, b in zip(row, v)) for row in inv(K))

@lru_cache(maxsize=None)
def cell_in(K, P):
    return all(min(coords(K, v)) >= 0 for v in P)

@lru_cache(maxsize=None)
def children(K):
    out = []
    for i, j in itertools.combinations(range(n), 2):
        s = add(K[i], K[j])
        c1 = list(K); c1[j] = s
        c2 = list(K); c2[i] = s
        out.append((cell(*c1), cell(*c2)))
    return tuple(out)

TREE = {}
def is_tree(D, K):
    key = (K, D)
    if key in TREE: return TREE[key]
    if len(D) == 1:
        r = (next(iter(D)) == K)
    else:
        r = False
        for K1, K2 in children(K):
            D1, D2, ok = [], [], True
            for P in D:
                if cell_in(K1, P): D1.append(P)
                elif cell_in(K2, P): D2.append(P)
                else: ok = False; break
            if ok and D1 and D2 and is_tree(frozenset(D1), K1) and is_tree(frozenset(D2), K2):
                r = True; break
    TREE[key] = r
    return r

def refines_E(U, Q):
    if len(U) < len(Q): return False
    groups = {l: [] for l in Q}
    for P in U:
        for l in Q:
            if cell_in(l, P): groups[l].append(P); break
        else:
            return False
    return all(g and is_tree(frozenset(g), l) for l, g in groups.items())

def refinements(P, Nmax):
    lev = {P}
    yield lev
    while len(next(iter(lev))) < Nmax:
        nxt = set()
        for D in lev:
            for l in D:
                rest = D - {l}
                for K1, K2 in children(l):
                    nxt.add(rest | {K1, K2})
            if len(nxt) > LEVEL_CAP: raise OverflowError(len(nxt))
        lev = nxt
        yield lev

PERMS = list(itertools.permutations(range(n)))
def pv(v, p): return tuple(v[p[i]] for i in range(n))
def act(D, p): return frozenset(cell(*(pv(v, p) for v in P)) for P in D)
def canon(D): return min(tuple(sorted(act(D, p))) for p in PERMS)
def in_frame(c, pieces): return frozenset(cell(*(coords(c, v) for v in P)) for P in pieces)
def restrict(U, l):
    D = in_frame(l, [P for P in U if cell_in(l, P)])
    return None if len(D) == 1 else canon(D)

def problem_leaves(U, Q):
    """Leaves of U that must still change for U >=_E Q: straddlers first; otherwise all leaves of Q-groups
    that are not yet split trees. Empty set means U >=_E Q."""
    groups = {l: [] for l in Q}
    strad = []
    for P in U:
        for l in Q:
            if cell_in(l, P): groups[l].append(P); break
        else:
            strad.append(P)
    if strad: return strad
    bad = []
    for l, g in groups.items():
        if not is_tree(frozenset(g), l): bad.extend(g)
    return bad

def cubs(A, B):
    """Guided search for common upper bounds: refine the larger element, splitting only problem leaves.
    Every returned U is verified exactly (U >=_E both). Not exhaustive; closure only needs existence."""
    P, Q = (A, B) if len(A) >= len(B) else (B, A)
    found, first, lev = [], None, {P}
    while lev:
        k = len(next(iter(lev)))
        if k > N or (first is not None and k > first + 1): break
        nxt = set()
        for U in lev:
            bad = problem_leaves(U, Q)
            if not bad:
                if refines_E(U, P) and refines_E(U, Q):
                    found.append(U)
                    if first is None: first = k
                continue
            for l in bad:
                rest = U - {l}
                for K1, K2 in children(l):
                    nxt.add(rest | {K1, K2})
            if len(nxt) > LEVEL_CAP: return found
        lev = nxt
    return found

def main():
    t0 = time.time()
    atoms = [frozenset(ch) for ch in children(DELTA)]
    S = {}
    for a in atoms: S.setdefault(canon(a), a)
    done = set()
    for ps in range(1, MAXPASS + 1):
        added, trunc, npairs = {}, [], 0
        items = list(S.items())
        for ca, A in items:
            for cb, B0 in items:
                if cb < ca: continue
                for B in {act(B0, p) for p in PERMS}:
                    key = (ca, tuple(sorted(B)))
                    if key in done: continue
                    done.add(key); npairs += 1
                    cand = cubs(A, B)
                    if not cand:
                        trunc.append([len(A), len(B)]); continue
                    best = None
                    for U in cand:
                        new = set()
                        for l in list(A) + list(B):
                            r = restrict(U, l)
                            if r is not None and r not in S and r not in added: new.add(r)
                        sc = (len(new), len(U))
                        if best is None or sc < best[0]: best = (sc, U, new)
                    for r in best[2]: added[r] = frozenset(r)
        S.update(added)
        hist = {}
        for r in added: hist[len(r)] = hist.get(len(r), 0) + 1
        rec = {"n": n, "pass": ps, "pairs": npairs, "added": len(added), "added_by_size": dict(sorted(hist.items())),
               "S_size": len(S), "max_element_size": max(len(k) for k in S), "pairs_without_cub": len(trunc),
               "secs": round(time.time() - t0, 1)}
        print(json.dumps(rec), flush=True)
        if trunc: print(json.dumps({"truncated_examples": trunc[:5]}), flush=True)
        if not added:
            print(json.dumps({"CLOSED" if not trunc else "STALLED_WITH_TRUNCATION": True, "S_size": len(S),
                              "sizes": sorted(len(k) for k in S)}), flush=True)
            break
    with open("closure_n%d.json" % n, "w") as f:
        json.dump({"n": n, "N": N, "S": [[list(map(list, c)) for c in k] for k in S]}, f)

if __name__ == "__main__":
    main()
