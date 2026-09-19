# Cone-propagation decision tree refuting a positive cone on Gamma^+ (radius-R ball), found by a
# lookahead DPLL (no SAT solver).  Same certificate format as dtree.py, checked by verify_cone.py.
# A node assumes a set A of positive elements; propagation closes P under products inside the ball
# (x, y in P, xy in ball => xy in P); a leaf is closed when x y = 1 with x, y in P.  At an open node
# every undecided g is probed on both sides; a g whose two sides both close gives a split with two
# leaves; a failed side (g closes) forces g^{-1} (recorded as a split whose first branch is a leaf);
# otherwise we branch on the g maximising the smaller closure.
# usage: dtree2.py census.json class [R] [maxleaves] [timeout_s] [short]
import sys, json, time
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import load, ball
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
path, ci = C + sys.argv[1], int(sys.argv[2])
R = int(sys.argv[3]) if len(sys.argv) > 3 else 4
MAXL = int(sys.argv[4]) if len(sys.argv) > 4 else 64
TMAX = float(sys.argv[5]) if len(sys.argv) > 5 else 600
SHORT = int(sys.argv[6]) if len(sys.argv) > 6 else None   # only products with a factor of length <= SHORT
T0 = time.time()
G = dict(load(path))[ci]
idx, els = ball(G, R)
K = [i for i, (v, h) in enumerate(els) if i > 0 and len(v) % 2 == 0 and len(h) % 2 == 0]
Kset = set(K)
def inv(g):
    return G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
INV = {i: idx[inv(els[i])] for i in K}
L = {a: [] for a in K}; Rr = {a: [] for a in K}      # L[a]: (b, a*b), Rr[a]: (b, b*a)
left = K if SHORT is None else [i for i in K if len(els[i][0]) + len(els[i][1]) <= SHORT]
seen = set()
for i in left:
    for j in K:
        for a, b in ((i, j), (j, i)):
            if (a, b) in seen: continue
            seen.add((a, b))
            k = idx.get(G.mul(els[a], els[b]))
            if k is not None and (k == 0 or k in Kset): L[a].append((b, k)); Rr[b].append((a, k))
del seen
class Closed(Exception): pass
def close(P, par, new):
    """extend P (set) and par (dict) in place by the closure of new; returns witness (x, y) or None"""
    todo = []
    for g in new:
        if g not in P: P.add(g); par[g] = None; todo.append(g)
    while todo:
        x = todo.pop()
        if INV[x] in P: return (x, INV[x])
        for lst in (L[x], Rr[x]):
            for (b, k) in lst:
                if b not in P: continue
                if k == 0: return (x, b) if lst is L[x] else (b, x)
                if k not in P: P.add(k); par[k] = (x, b) if lst is L[x] else (b, x); todo.append(k)
    return None
def word(i):
    v, h = els[i]
    return ''.join('v%d' % x for x in v) + ''.join('h%d' % x for x in h)
def leaf(par, w):
    steps = []; seen = set()
    def need(x):
        if x in seen or par[x] is None: return
        seen.add(x); need(par[x][0]); need(par[x][1]); steps.append([word(x), word(par[x][0]), word(par[x][1])])
    need(w[0]); need(w[1])
    return ['leaf', [word(w[0]), word(w[1])], steps]
cands = sorted(set(min(i, INV[i]) for i in K), key=lambda i: len(els[i][0]) + len(els[i][1]))
nleaves = 0
class Budget(Exception): pass
def solve(A, depth):
    """returns a tree refuting assumption set A, or None"""
    global nleaves
    if time.time() - T0 > TMAX or nleaves > MAXL: raise Budget
    P = set(); par = {}
    w = close(P, par, A)
    if w: nleaves += 1; return leaf(par, w)
    if depth == 0: return None
    best = None
    for g in cands:
        if g in P or INV[g] in P: continue
        P1 = set(P); p1 = dict(par); w1 = close(P1, p1, [g])
        P2 = set(P); p2 = dict(par); w2 = close(P2, p2, [INV[g]])
        if w1 and w2:
            return ['split', word(g), solve(A | {g}, 0), solve(A | {INV[g]}, 0)]
        if w1 or w2:
            # failed literal: one side closes; continue on the other side only
            if w1:
                t1 = solve(A | {g}, 0); t2 = solve(A | {INV[g]}, depth)
                return ['split', word(g), t1, t2] if t2 else None
            t2 = solve(A | {INV[g]}, 0); t1 = solve(A | {g}, depth)
            return ['split', word(g), t1, t2] if t1 else None
        sc = min(len(P1), len(P2))
        if best is None or sc > best[0]: best = (sc, g)
    if best is None: return None
    g = best[1]
    t1 = solve(A | {g}, depth - 1)
    if t1 is None: return None
    t2 = solve(A | {INV[g]}, depth - 1)
    if t2 is None: return None
    return ['split', word(g), t1, t2]
res = None
try:
    for d in range(1, 12):
        nleaves = 0
        t = solve(frozenset(), d)
        if t: res = dict(cls=ci, R=R, depth=d, leaves=nleaves, tree=t); break
        print('no tree of lookahead depth', d, flush=True)
except Budget:
    print('budget exhausted: leaves', nleaves, 'time %.0f' % (time.time() - T0), flush=True)
if res: print(json.dumps(res))
