# Extract a deletion-minimal non-left-orderability certificate for the subgroup
#   M = < x, y, f x^-1 f, g y^-1 g >  of Gamma^+,   x = v_i v_j,  y = h_k h_l,  f = v_f,  g = h_g,
# of a census class, from the positive-cone ball instance of radius R (in the 4 generators and their
# inverses) with one factor of length <= short.
# usage: certgen.py census.json class R short i j f k l g out.json
import sys, json
from pysat.solvers import Cadical153
sys.path.insert(0, '../bmw-census-left-orders-2026-09-17')
from lo_census import VH
census, ci, R, short, i, j, f, k, l, g, out = sys.argv[1], *map(int, sys.argv[2:11]), sys.argv[11]
SQ = {tuple(a): tuple(b) for a, b in json.load(open(census))['reps'][ci]}
G = VH(list(range(4)), list(range(4)), SQ); G.confluence()
def inv(z):
    return G.mul(((), tuple(G.iA[x] for x in reversed(z[1]))), (tuple(G.iB[x] for x in reversed(z[0])), ()))
M = G.mul
gens = [((i, j), ()), ((), (k, l)), M(M(((f,), ()), ((j, i), ())), ((f,), ())), M(M(((), (g,)), ((), (l, k))), ((), (g,)))]
gens4 = list(gens)
gens = gens + [inv(z) for z in gens]
e = ((), ()); idx = {e: 0}; els = [e]; ln = [0]; layer = [e]
for d in range(R):
    nl = []
    for z in layer:
        for x in gens:
            y = M(z, x)
            if y not in idx: idx[y] = len(els); els.append(y); ln.append(d + 1); nl.append(y)
    layer = nl
n = len(els)
hard = []
for a in range(1, n):
    b = idx[inv(els[a])]; assert b != a
    if a < b: hard += [[a, b], [-a, -b]]
rels = set()
for a in range(1, n):
    if ln[a] > short: continue
    for b in range(1, n):
        for (p, q) in ((a, b), (b, a)):
            c = idx.get(M(els[p], els[q]))
            if c is not None: rels.add((p, q, c))
rels = sorted(rels)
def core_of(rs):
    with Cadical153(bootstrap_with=hard) as S:
        for r, (p, q, c) in enumerate(rs):
            S.add_clause(([-p, -q] if c == 0 else [-p, -q, c]) + [-(n + 1 + r)])
        if S.solve(assumptions=[n + 1 + r for r in range(len(rs))]): return None
        return [rs[x - n - 1] for x in S.get_core()]
rs = rels
c = core_of(rs)
if c is None:
    print('class', ci, 'SAT: no certificate at this radius'); sys.exit(1)
while True:
    c = core_of(rs)
    if len(c) == len(rs): break
    rs = sorted(c)
t = 0
while t < len(rs):
    trial = rs[:t] + rs[t + 1:]
    c = core_of(trial)
    if c is None: t += 1
    else: rs = sorted(c) if len(c) < len(trial) else trial
used = sorted({x for r in rs for x in r if x != 0})
def fmt(z): return ''.join('v%d' % x for x in z[0]) + '|' + ''.join('h%d' % x for x in z[1])
json.dump({'class': ci, 'generators': [fmt(z) for z in gens4], 'R': R, 'short': short,
           'elements': {str(u): fmt(els[u]) for u in used},
           'relations': [[p, q, c] for p, q, c in rs]}, open(out, 'w'), indent=0)
print('class', ci, 'generators', [fmt(z) for z in gens4], 'ball', n, 'minimal core relations', len(rs),
      'elements', len(used))
