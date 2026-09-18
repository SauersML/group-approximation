#!/usr/bin/env python3
# bh-free-61: spine of the edge-split operad O_E at m = 2, and Thumann splitting categories A(Theta).
# Cells: sorted triples of integer column vectors (frame modulo S_3). Dissections: frozensets of cells.
# D >=_E Q  <=>  every piece of D lies in a leaf of Q and the pieces in each leaf form a split tree of it.
# mcub(P, Q): minimal common >=_E upper bounds, found exactly among refinements of P with at most N pieces.
# Spine: start from the three atoms; iterate mcubs of pairs (Thumann Construction 45209).
# A(Theta): proper factorizations Theta = D' o (blocks), each block a spine element in its cell's frame or a
# single piece, D' in O_E with >= 2 pieces; ordered by >=_E; we report connected components.
import sys, json, time, itertools
from functools import lru_cache

def add(u, v): return (u[0]+v[0], u[1]+v[1], u[2]+v[2])
def cell(a, b, c): return tuple(sorted((a, b, c)))
E0, E1, E2 = (1,0,0), (0,1,0), (0,0,1)
DELTA = cell(E0, E1, E2)

def det3(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0]))

@lru_cache(maxsize=None)
def inv(K):
    a, b, c = K; d = det3(a, b, c)
    # rows of K^{-1}: (b x c)/d, (c x a)/d, (a x b)/d  (columns a, b, c)
    def cr(x, y): return (x[1]*y[2]-x[2]*y[1], x[2]*y[0]-x[0]*y[2], x[0]*y[1]-x[1]*y[0])
    r = (cr(b, c), cr(c, a), cr(a, b))
    return tuple(tuple(x // d for x in row) for row in r), d

def coords(K, v):
    r, d = inv(K)
    return tuple(row[0]*v[0]+row[1]*v[1]+row[2]*v[2] for row in r)

@lru_cache(maxsize=None)
def cell_in(K, P):
    return all(min(coords(K, v)) >= 0 for v in P)

def children(K):
    a, b, c = K
    out = []
    for (x, y, z) in ((a, b, c), (a, c, b), (b, c, a)):
        s = add(x, y)
        out.append((cell(x, s, z), cell(s, y, z)))
    return out

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

LEVEL_CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 400000
def refinements(P, N):
    """Lazily yield the levels of O_E refinements of P, up to N pieces (P itself first).
    Raises OverflowError if a level exceeds LEVEL_CAP (reported, never silently truncated)."""
    lev = {P}
    yield lev
    while len(next(iter(lev))) < N:
        nxt = set()
        for D in lev:
            for l in D:
                rest = D - {l}
                for K1, K2 in children(l):
                    nxt.add(rest | {K1, K2})
            if len(nxt) > LEVEL_CAP: raise OverflowError(len(nxt))
        lev = nxt
        yield lev

def permute(v, p): return (v[p[0]], v[p[1]], v[p[2]])
PERMS = list(itertools.permutations(range(3)))
def canon(D):
    best = None
    for p in PERMS:
        t = tuple(sorted(cell(permute(a, p), permute(b, p), permute(c, p)) for (a, b, c) in D))
        if best is None or t < best: best = t
    return best

SPAN = 2
def mcubs(P, Q, N):
    """Minimal common upper bounds among refinements of the larger element, from the first level that has a
    common upper bound through SPAN more levels (and never beyond N pieces). Exact minimality inside that range."""
    if len(P) < len(Q): P, Q = Q, P
    cub, first = [], None
    try:
        for lev in refinements(P, N):
            k = len(next(iter(lev)))
            if first is not None and k > first + SPAN: break
            for U in lev:
                if refines_E(U, Q):
                    cub.append(U)
                    if first is None: first = k
    except OverflowError:
        pass
    cub.sort(key=len)
    mins = []
    for U in cub:
        if not any(len(V) < len(U) and refines_E(U, V) for V in mins):
            mins.append(U)
    return mins, len(cub)

def atoms():
    return [frozenset(ch) for ch in children(DELTA)]

def in_frame(c, block):
    """Pieces of block expressed in the frame of cell c (columns of c as the standard basis)."""
    return frozenset(cell(coords(c, P[0]), coords(c, P[1]), coords(c, P[2])) for P in block)

def union_cell(block):
    """If the pieces tile a unimodular cone, return it (else None). Candidate rays: extreme rays among piece rays."""
    rays = sorted({v for P in block for v in P})
    for tri in itertools.combinations(rays, 3):
        if abs(det3(*tri)) != 1: continue
        c = cell(*tri)
        if not all(cell_in(c, P) for P in block): continue
        # tiling check: Egyptian weights in c's frame sum to 1  (weight = 1 / prod(height))
        from fractions import Fraction
        s = Fraction(0)
        for P in block:
            w = 1
            for v in P: w *= sum(coords(c, v))
            s += Fraction(1, w)
        if s == 1: return c
    return None

def splitting_category(Theta, spine_canon):
    pieces = sorted(Theta)
    n = len(pieces)
    sizes = sorted({len(s) for s in spine_canon})
    blocks = []   # (frozenset of pieces, cell)
    for k in sizes:
        if k > n: continue
        for sub in itertools.combinations(pieces, k):
            fs = frozenset(sub)
            c = union_cell(fs)
            if c is None or c == DELTA and k == n: continue
            if canon(in_frame(c, fs)) in spine_canon: blocks.append((fs, c))
    # families of pairwise disjoint blocks (nonempty)
    elems = []
    def rec(i, used, chosen):
        if chosen:
            Dp = frozenset((Theta - used) | {c for (_, c) in chosen})
            if len(Dp) >= 2 and is_tree(Dp, DELTA): elems.append(Dp)
        for j in range(i, len(blocks)):
            fs, c = blocks[j]
            if fs & used: continue
            rec(j + 1, used | fs, chosen + [(fs, c)])
    rec(0, frozenset(), [])
    elems = list(set(elems))
    # comparability graph components
    parent = list(range(len(elems)))
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    edges = 0
    for i in range(len(elems)):
        for j in range(len(elems)):
            if i != j and len(elems[i]) > len(elems[j]) and refines_E(elems[i], elems[j]):
                edges += 1; parent[find(i)] = find(j)
    comps = len({find(i) for i in range(len(elems))})
    return {"elements": len(elems), "comparabilities": edges, "components": comps, "blocks": len(blocks)}

def act(D, p):
    return frozenset(cell(permute(a, p), permute(b, p), permute(c, p)) for (a, b, c) in D)

def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    t0 = time.time()
    S = set(atoms())
    print(json.dumps({"N": N, "LEVEL_CAP": LEVEL_CAP, "SPAN": SPAN}), flush=True)                      # actual dissections of Delta, closed under S_3
    new = set(S)
    out = {"N": N, "rounds": []}
    for r in range(1, rounds + 1):
        found, trunc, npairs = set(), 0, 0
        reps = {}
        for P in S: reps.setdefault(canon(P), P)       # one representative per S_3-orbit
        for P in reps.values():
            orbitP = {act(P, p) for p in PERMS}
            for Q in S:
                if not (orbitP & new) and Q not in new: continue
                npairs += 1
                ms, ncub = mcubs(P, Q, N)
                if ncub == 0: trunc += 1
                for U in ms:
                    for p in PERMS:
                        V = act(U, p)
                        if V not in S: found.add(V)
        new = found
        S |= found
        hist = {}
        for U in new: hist[len(U)] = hist.get(len(U), 0) + 1
        out["rounds"].append({"round": r, "pairs": npairs, "new": len(new), "new_by_size": dict(sorted(hist.items())),
                              "pairs_without_cub_in_window": trunc, "secs": round(time.time()-t0, 1)})
        print(json.dumps(out["rounds"][-1]), flush=True)
        if not new: break
    spine_canon = {canon(U) for U in S}
    res = []
    reps = {}
    for U in S: reps.setdefault(canon(U), U)
    for cu, U in sorted(reps.items(), key=lambda kv: (len(kv[1]), kv[0])):
        if len(U) < 3: continue
        a = splitting_category(U, spine_canon)
        a["size"] = len(U); a["orbit"] = len({act(U, p) for p in PERMS}); a["canon"] = [list(map(list, c)) for c in cu]
        res.append(a)
        print(json.dumps({"A": {k: a[k] for k in ("size", "orbit", "elements", "comparabilities", "components", "blocks")}}), flush=True)
    out["spine_size"] = len(S); out["splitting"] = res; out["secs"] = round(time.time()-t0, 1)
    with open("spine.%d.json" % N, "w") as f: json.dump(out, f)
    print(json.dumps({"spine_size": len(S), "orbits": len(reps), "secs": out["secs"]}))

if __name__ == "__main__":
    main()
