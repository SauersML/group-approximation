"""Symmetric candidates: unions of orbits of integral anti-flags under a finite subgroup G of GL_3(Z).

Every union S of G-orbits gives a G-invariant reflection configuration.  We check the exact
local faithfulness rules R0-R3 (see round5.py) and positive Euler characteristic, then run the
exact kernel search.  usage: orbits.py B maxorbits klen [group]
group: 'hyper' = signed permutation matrices (order 48), 'hex' = order-24 hexagonal group.
"""
import sys, itertools, numpy as np
import antiflag as AF
from driver import test_subgraph

B = int(sys.argv[1]); MAXO = int(sys.argv[2]); klen = int(sys.argv[3])
grp = sys.argv[4] if len(sys.argv) > 4 else 'hyper'


def group_mats(name):
    mats = []
    if name == 'hyper':
        for perm in itertools.permutations(range(3)):
            for signs in itertools.product((1, -1), repeat=3):
                M = np.zeros((3, 3), dtype=np.int64)
                for i, j in enumerate(perm):
                    M[i, j] = signs[i]
                mats.append(M)
    else:
        r = np.array([[1, -1, 0], [1, 0, 0], [0, 0, 1]])  # order 6 on the hexagonal lattice
        f = np.array([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
        z = np.diag([1, 1, -1])
        gens = [r, f, z]
        seen = {np.eye(3, dtype=np.int64).tobytes(): np.eye(3, dtype=np.int64)}
        frontier = list(seen.values())
        while frontier:
            new = []
            for M in frontier:
                for g in gens:
                    N = g @ M
                    if N.tobytes() not in seen:
                        seen[N.tobytes()] = N; new.append(N)
            frontier = new
        mats = list(seen.values())
    return mats


def canon(p, L):
    nz = next(c for c in p if c != 0)
    if nz < 0:
        p = tuple(-c for c in p); L = tuple(-c for c in L)
    return (tuple(int(c) for c in p), tuple(int(c) for c in L), abs(AF.dot(p, L)))


G = group_mats(grp)
verts = AF.build(B)
index = {x: i for i, x in enumerate(verts)}
orbits = []; done = set()
for x in verts:
    if x in done:
        continue
    orb = set()
    for M in G:
        p = M @ np.array(x[0]); L = np.linalg.inv(M).T.round().astype(np.int64) @ np.array(x[1])
        y = canon(tuple(p), tuple(L))
        orb.add(y)
    done |= orb
    if all(y in index for y in orb):
        orbits.append(sorted(index[y] for y in orb))
print("group", grp, len(G), "B", B, "antiflags", len(verts), "orbits", len(orbits), flush=True)
A, bad = AF.graph(verts)
cid = [x[0] for x in verts]; aid = [x[1] for x in verts]


def check(S):
    S = list(S); Sset = set(S)
    for v in S:
        if bad[v] & Sset:
            return 'bad'
    Ad = {v: A[v] & Sset for v in S}
    for v in S:
        for u in Ad[v]:
            if Ad[u] & Ad[v]:
                return 'triangle'
    for u, w in itertools.combinations(S, 2):
        if w not in Ad[u] and len(Ad[u] & Ad[w]) >= 3:
            return 'K23'
    byc = {}; bya = {}
    for v in S:
        byc.setdefault(cid[v], []).append(v); bya.setdefault(aid[v], []).append(v)
    if any(len(g) > 2 for g in byc.values()) or any(len(g) > 2 for g in bya.values()):
        return 'R1'
    for p, g in byc.items():
        if len(g) == 2:
            for x in S:
                if x not in g and AF.dot(aid[x], p) == 0 and not (g[0] in Ad[x] and g[1] in Ad[x]):
                    return 'R2'
    for L, g in bya.items():
        if len(g) == 2:
            for x in S:
                if x not in g and AF.dot(L, cid[x]) == 0 and not (g[0] in Ad[x] and g[1] in Ad[x]):
                    return 'R3'
    E = sum(len(Ad[v]) for v in S) // 2
    return 4 - 2 * len(S) + E


stats = {}
best = None
for k in range(1, MAXO + 1):
    for combo in itertools.combinations(range(len(orbits)), k):
        S = set().union(*(orbits[i] for i in combo))
        r = check(S)
        key = r if isinstance(r, str) else ('pos' if r > 0 else 'nonpos')
        stats[key] = stats.get(key, 0) + 1
        if not isinstance(r, str) and (best is None or r > best[0]):
            best = (r, combo, len(S))
        if not isinstance(r, str) and r > 0:
            found, L, tot = test_subgraph(verts, S, A, max_len=klen, max_elems=200000)
            print("POS 4chi", r, "V", len(S), "orbits", combo, "kernel", found[:1], "len", L, "elems", tot, flush=True)
    print("k", k, stats, "best", best, flush=True)
