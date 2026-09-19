# Smallest cone-propagation decision tree refuting a positive cone on Gamma^+ (radius-R ball).
# A node assumes signs for some elements; propagation closes the assumed-positive set P under
# products inside the ball (x, y in P, xy in ball  =>  xy in P); a leaf is closed when 1 in P
# (some x y = 1 with x, y in P).  Branch on g: either g in P or g^{-1} in P.
# usage: dtree.py census.json class [R] [maxdepth]
import sys, json
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import load, ball
path, ci = sys.argv[1], int(sys.argv[2])
R = int(sys.argv[3]) if len(sys.argv) > 3 else 4; MAXD = int(sys.argv[4]) if len(sys.argv) > 4 else 4
G = dict(load(path))[ci]
idx, els = ball(G, R)
K = [i for i, (v, h) in enumerate(els) if i > 0 and len(v) % 2 == 0 and len(h) % 2 == 0]
Kset = set(K)
def inv(g):
    return G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
INV = {i: idx[inv(els[i])] for i in K}
PROD = {}
for a in K:
    for b in K:
        k = idx.get(G.mul(els[a], els[b]))
        if k is not None and (k == 0 or k in Kset): PROD[a, b] = k
BY = {}
for (a, b), k in PROD.items(): BY.setdefault(a, []).append((b, k)); BY.setdefault(b, []).append((a, k))
def close(P):
    """closure; returns (P, None) or (P, witness) with witness a pair (x, y) with x y = 1."""
    P = set(P); todo = list(P); par = {x: None for x in P}
    while todo:
        x = todo.pop(0)
        if INV[x] in P: return P, (x, INV[x], par)
        for a in list(P):
            for (u, v) in ((x, a), (a, x)):
                k = PROD.get((u, v))
                if k is None: continue
                if k == 0: return P, (u, v, par)
                if k not in P: P.add(k); todo.append(k); par[k] = (u, v)
    return P, None
def word(i):
    v, h = els[i]
    return ''.join('v%d' % x for x in v) + ''.join('h%d' % x for x in h)
cands = sorted(set(min(i, INV[i]) for i in K), key=lambda i: len(els[i][0]) + len(els[i][1]))
def solve(A, depth):
    P, w = close(A)
    if w:
        par = w[2]; steps = []; seen = set()
        def need(x):
            if x in seen or par[x] is None: return
            seen.add(x); need(par[x][0]); need(par[x][1]); steps.append([word(x), word(par[x][0]), word(par[x][1])])
        need(w[0]); need(w[1])
        return ('leaf', [word(w[0]), word(w[1])], steps), 1 + len(steps) / 1000
    if depth == 0: return None, None
    best = None
    for g in cands:
        if g in P or INV[g] in P: continue
        t1, n1 = solve(A | {g}, depth - 1)
        if t1 is None: continue
        t2, n2 = solve(A | {INV[g]}, depth - 1)
        if t2 is None: continue
        if best is None or n1 + n2 < best[1]:
            best = (('split', word(g), t1, t2), n1 + n2)
            pass
    return best if best else (None, None)
for d in range(1, MAXD + 1):
    t, n = solve(set(), d)
    if t:
        print(json.dumps(dict(cls=ci, R=R, depth=d, leaves=n, tree=t))); break
    print('no tree of depth', d, flush=True)
