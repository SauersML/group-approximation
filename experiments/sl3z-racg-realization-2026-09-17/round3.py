"""Annealing over induced subgraphs of the integral anti-flag graph, forbidding
triangles, K_{2,3}, finite-order non-edges, and pair collisions s_a s_b = s_c s_d; then exact kernel search."""
import sys, math, random, numpy as np
import antiflag as AF
from driver import test_subgraph

B = int(sys.argv[1]); iters = int(sys.argv[2]); seeds = int(sys.argv[3]); klen = int(sys.argv[4])
verts = AF.build(B); A, bad = AF.graph(verts)
NOPARA = int(sys.argv[5]) if len(sys.argv) > 5 else 1
if NOPARA:  # forbid non-edges with a_uw a_wu in [0,4]: every non-edge dihedral is loxodromic
    for i in range(len(verts)):
        for j in range(i + 1, len(verts)):
            if j in A[i]: continue
            pr = round(AF.cartan(verts[i], verts[j]) * AF.cartan(verts[j], verts[i]))
            if 0 <= pr <= 4:
                bad[i].add(j); bad[j].add(i)
R = [AF.reflection(x) for x in verts]
print("B", B, "antiflags", len(verts), flush=True)

def pair_keys(S, v):
    out = []
    for w in S:
        if w in A[v]:
            out.append((R[v] @ R[w]).tobytes())  # commuting pair: one product
        else:
            out.append((R[v] @ R[w]).tobytes()); out.append((R[w] @ R[v]).tobytes())
    return out

def anneal(seed):
    rng = random.Random(seed); n = len(verts)
    S = set(); E = 0; prods = {}
    best = (-10**9, None)
    for it in range(iters):
        T = 2.0 * (1 - it / iters) + 0.05
        v = rng.randrange(n)
        if v in S:
            dE = len(A[v] & S); d = 2 - dE
            if d >= 0 or rng.random() < math.exp(d / T):
                S.remove(v); E -= dE
                for k in pair_keys(S, v):
                    prods[k] -= 1
                    if prods[k] == 0: del prods[k]
        else:
            dE = len(A[v] & S); d = dE - 2
            if not (d >= 0 or rng.random() < math.exp(d / T)):
                continue
            if not AF.ok_add(S, v, A, bad):
                continue
            ks = pair_keys(S, v)
            if len(set(ks)) < len(ks) or any(k in prods for k in ks) or R[v].tobytes() in prods or np.array_equal(R[v], np.eye(3)):
                continue
            S.add(v); E += dE
            for k in ks: prods[k] = prods.get(k, 0) + 1
        sc = 4 - 2 * len(S) + E
        if len(S) > 2 and sc > best[0]:
            best = (sc, set(S))
    return best

for seed in range(seeds):
    sc, S = anneal(seed)
    E = sum(len(A[v] & S) for v in S) // 2
    print(f"seed={seed} 4chi={sc} V={len(S)} E={E}", flush=True)
    if sc > 0:
        found, L, tot = test_subgraph(verts, S, A, max_len=klen, max_elems=300000)
        idx = sorted(S)
        print("  kernel:", [([verts[idx[i]] for i in w1], [verts[idx[i]] for i in w2]) for w1, w2 in found], "len", L, "elems", tot, flush=True)
