# sgen.py in.jsonl k R short [stop] : the subgroup-cone search of ../bmw-44-survivor-left-orders-2026-09-17/
# gen_search.py, for any degrees.  Tries every M = <x, y, f x^-1 f, g y^-1 g> with x = v_i v_j, y = h_k h_l,
# f a v-letter not in {i,j}, g an h-letter not in {k,l} (letters are involutions here), and reports the
# ones whose positive-cone instance on the radius-R ball of M (one factor of length <= short) is UNSAT.
# A hit is only a lead: sgcert.py turns it into a checked certificate.
import sys, json, time, itertools
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import VH, solve
from vh_enum import inv_arr
def group(r):
    m, pA, n, pB = int(r['pat'][0]), int(r['pat'][1]), int(r['pat'][3]), int(r['pat'][4])
    G = VH(inv_arr(m, pA), inv_arr(n, pB), {tuple(a): tuple(b) for a, b in r['sq']}); G.confluence(); return G, m, n
def inv(G, g):
    return G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
def gens_of(G, i, j, f, k, l, g):
    return [((i, j), ()), ((), (k, l)), G.mul(G.mul(((f,), ()), ((j, i), ())), ((f,), ())),
            G.mul(G.mul(((), (g,)), ((), (l, k))), ((), (g,)))]
def instance(G, gens, R, short):
    gens = gens + [inv(G, g) for g in gens]
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
        j = idx.get(inv(G, els[i]))
        if j is not None and i < j: cl += [[i, j], [-i, -j]]
    for a in range(1, len(els)):
        if ln[a] > short: continue
        for b in range(1, len(els)):
            for (p, q) in ((a, b), (b, a)):
                k = idx.get(G.mul(els[p], els[q]))
                if k is not None: cl.append([-p, -q] if k == 0 else [-p, -q, k])
    return els, cl
if __name__ == '__main__':
    r = [json.loads(l) for l in open(sys.argv[1])][int(sys.argv[2])]
    R, short = int(sys.argv[3]), int(sys.argv[4]); stop = len(sys.argv) > 5
    G, m, n = group(r); t0 = time.time(); found = tried = 0
    for (i, j) in itertools.combinations(range(n), 2):
        for f in [z for z in range(n) if z not in (i, j)]:
            for (k, l) in itertools.combinations(range(m), 2):
                for g in [z for z in range(m) if z not in (k, l)]:
                    els, cl = instance(G, gens_of(G, i, j, f, k, l, g), R, short); tried += 1
                    if not solve(cl, both=False):
                        found += 1
                        print('UNSAT', json.dumps([i, j, f, k, l, g]), 'ball', len(els), round(time.time() - t0), 's', flush=True)
                        if stop: sys.exit(0)
    print('done', r['pat'], r['seed'], 'R', R, 'short', short, 'tried', tried, 'UNSAT', found, round(time.time() - t0), 's', flush=True)
