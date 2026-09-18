"""Annealing with the exact local faithfulness rules of the reflection-realization normal form.

Rules on an induced vertex set S of the integral anti-flag graph (all necessary for faithfulness):
  R0 no finite-order non-edge; triangle-free; K_{2,3}-free; no pair collision s_a s_b = s_c s_d
  R1 at most two members of S share a centre, at most two share an axis
  R2 if p_a = p_b = p (a != b), every x in S \ {a,b} whose axis contains p is adjacent to a and b
  R3 dually, if L_a = L_b = L, every x in S \ {a,b} whose centre lies on L is adjacent to a and b
Then exact kernel search on the best set.
usage: round5.py B iters seeds klen
"""
import sys, math, random, numpy as np
import antiflag as AF
from driver import test_subgraph

B = int(sys.argv[1]); iters = int(sys.argv[2]); seeds = int(sys.argv[3]); klen = int(sys.argv[4])
verts = AF.build(B); A, bad = AF.graph(verts)
R = [AF.reflection(x) for x in verts]
n = len(verts)
print("B", B, "antiflags", n, flush=True)
cen = [x[0] for x in verts]; axi = [x[1] for x in verts]
canon = lambda v: v  # prim_vectors are already sign-canonical; axes carry the sign making L.p > 0
def ckey(v):
    nz = next(c for c in v if c != 0)
    return v if nz > 0 else tuple(-c for c in v)
cid = [ckey(c) for c in cen]; aid = [ckey(a) for a in axi]
dot = AF.dot


def local_ok(S, v):
    # R1
    sc = [a for a in S if cid[a] == cid[v]]
    sa = [a for a in S if aid[a] == aid[v]]
    if len(sc) >= 2 or len(sa) >= 2:
        return False
    # R2 with v as a new sharer
    if sc:
        a = sc[0]; p = cen[v]
        for x in S:
            if x != a and dot(axi[x], p) == 0 and not (x in A[a] and x in A[v]):
                return False
    if sa:
        a = sa[0]; L = axi[v]
        for x in S:
            if x != a and dot(L, cen[x]) == 0 and not (x in A[a] and x in A[v]):
                return False
    # R2/R3 with v as a new incident vertex of an existing shared pair
    seenc = {}; seena = {}
    for a in S:
        seenc.setdefault(cid[a], []).append(a); seena.setdefault(aid[a], []).append(a)
    for key, pair in seenc.items():
        if len(pair) == 2 and key != cid[v] and dot(axi[v], cen[pair[0]]) == 0:
            if not (pair[0] in A[v] and pair[1] in A[v]):
                return False
    for key, pair in seena.items():
        if len(pair) == 2 and key != aid[v] and dot(axi[pair[0]], cen[v]) == 0:
            if not (pair[0] in A[v] and pair[1] in A[v]):
                return False
    return True


def pair_keys(S, v):
    out = []
    for w in S:
        out.append((R[v] @ R[w]).tobytes())
        if w not in A[v]:
            out.append((R[w] @ R[v]).tobytes())
    return out


def anneal(seed):
    rng = random.Random(seed)
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
            if not AF.ok_add(S, v, A, bad) or not local_ok(S, v):
                continue
            ks = pair_keys(S, v)
            if len(set(ks)) < len(ks) or any(k in prods for k in ks):
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
