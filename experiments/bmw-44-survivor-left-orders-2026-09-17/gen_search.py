# For a census class, search 4-generator subgroups <x, y, f x^-1 f, g y^-1 g> of Gamma^+ with
# x = v_i v_j, y = h_k h_l, f not in {i,j}, g not in {k,l}, for an UNSAT positive-cone ball instance
# (ball radius R in the 4 generators, one factor of length <= short).  This is the pattern of the
# #281 certificate (x = v0v1, y = h0h1, f = v3, g = h3).
# usage: gen_search.py class R short   (run from this directory)
import sys, json, time, itertools
sys.path.insert(0, '../bmw-census-left-orders-2026-09-17')
from lo_census import VH, solve
D = json.load(open('../bmw-census-left-orders-2026-09-17/census_40_40.json'))
cls_i, R, short = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
SQ = {tuple(a): tuple(b) for a, b in D['reps'][cls_i]}
G = VH(list(range(4)), list(range(4)), SQ); G.confluence()
def inv(g):
    return G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
def ballsat(gens):
    gens = gens + [inv(g) for g in gens]
    e = ((), ()); idx = {e: 0}; els = [e]; ln = [0]; layer = [e]
    for d in range(R):
        nl = []
        for g in layer:
            for x in gens:
                y = G.mul(g, x)
                if y not in idx: idx[y] = len(els); els.append(y); ln.append(d + 1); nl.append(y)
        layer = nl
    cl = []
    for i in range(1, len(els)):
        j = idx.get(inv(els[i]))
        if j is not None and i < j: cl += [[i, j], [-i, -j]]
    for a in range(1, len(els)):
        if ln[a] > short: continue
        for b in range(1, len(els)):
            for (p, q) in ((a, b), (b, a)):
                k = idx.get(G.mul(els[p], els[q]))
                if k is not None: cl.append([-p, -q] if k == 0 else [-p, -q, k])
    return len(els), solve(cl, both=False)
pairs = list(itertools.combinations(range(4), 2))
t0 = time.time(); found = 0
for (i, j) in pairs:
    for f in [z for z in range(4) if z not in (i, j)]:
        for (k, l) in pairs:
            for g in [z for z in range(4) if z not in (k, l)]:
                gens = [((i, j), ()), ((), (k, l)), (G.mul(G.mul(((f,), ()), ((j, i), ())), ((f,), ())) ),
                        G.mul(G.mul(((), (g,)), ((), (l, k))), ((), (g,)))]
                n, r = ballsat(gens)
                tag = 'v%d v%d f=v%d | h%d h%d g=h%d' % (i, j, f, k, l, g)
                if not r:
                    found += 1; print('UNSAT', cls_i, tag, 'ball', n, round(time.time() - t0), 's', flush=True)
print('class', cls_i, 'R', R, 'short', short, 'done; UNSAT instances:', found, round(time.time() - t0), 's', flush=True)
