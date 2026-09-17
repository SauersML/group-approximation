#!/usr/bin/env python3
"""Monte Carlo sanity check (not part of any proof): fraction of clusters of the
identity reaching a size cap on Cay(F_3 x Z, S) with
S = {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(c,0),(c,1),(c,5),(1,1)}^{+-1}.
Usage: mc_rank3_rigid.py p cap trials seed"""
import random, sys
D = {1: [0, 1, 3], 2: [0, 1, 4], 3: [0, 1, 5]}
def nbrs(v):
    w, k = v
    for s in (1, 2, 3):
        for sg in (1, -1):
            l = s * sg
            nw = w[:-1] if (w and w[-1] == -l) else w + (l,)
            for j in D[s]:
                yield (nw, k + sg * j)
    yield (w, k + 1); yield (w, k - 1)
def explore(p, cap, rng):
    o = ((), 0); seen = {o}; stack = [o]; st = {}
    while stack:
        v = stack.pop()
        for u in nbrs(v):
            e = (v, u) if (len(v[0]), v) < (len(u[0]), u) else (u, v)
            if e not in st:
                st[e] = rng.random() < p
            if st[e] and u not in seen:
                seen.add(u); stack.append(u)
                if len(seen) >= cap:
                    return cap
    return len(seen)
p, cap, trials, seed = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
sizes = [explore(p, cap, rng) for _ in range(trials)]
print(f"p={p} cap={cap} trials={trials} frac_cap={sum(s>=cap for s in sizes)/trials:.3f} mean={sum(sizes)/trials:.1f}")
