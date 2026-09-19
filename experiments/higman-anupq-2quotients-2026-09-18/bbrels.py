"""Short relators of Bbar_e = <b,d> from its right regular representation (levels_ck.py tables).

BFS on the Cayley graph (generators b, d, b^-1, d^-1) from the identity gives a geodesic word w(g)
for every element g.  Every non-tree edge g -> g x gives the relator w(g) x w(gx)^-1 (it holds in
Bbar_e by construction).  We keep the first NREL distinct ones (freely and cyclically reduced,
deduplicated up to cyclic permutation and inversion), in BFS order, i.e. shortest first.
Each relator is re-checked on the tables before it is printed.
usage: python3 bbrels.py e K NREL > rels-e<e>.txt   (pq word syntax, one relator per line)
"""
import sys
import numpy as np
e, K, NREL = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
z = np.load('ck%d/L%d.npz' % (e, K))
Rb, Rd = z['Rb'].astype(np.int64), z['Rd'].astype(np.int64)
N = len(Rb)
Rbi = np.empty(N, np.int64); Rbi[Rb] = np.arange(N)
Rdi = np.empty(N, np.int64); Rdi[Rd] = np.arange(N)
T = {1: Rb, 2: Rd, -1: Rbi, -2: Rdi}   # letter -> right-multiplication table
par = -np.ones(N, np.int64); plet = np.zeros(N, np.int64); dep = -np.ones(N, np.int64)
par[0] = 0; dep[0] = 0
front = np.array([0], np.int64)
rels = []; seen = set()

def word(g):
    w = []
    while g != 0:
        w.append(int(plet[g])); g = int(par[g])
    return w[::-1]

def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    while len(out) > 1 and out[0] == -out[-1]:
        out = out[1:-1]
    return out

def canon(w):
    n = len(w); best = None
    for v in (w, [-x for x in w[::-1]]):
        for i in range(n):
            c = tuple(v[i:] + v[:i])
            if best is None or c < best: best = c
    return best

def evaluate(w):
    g = 0
    for x in w: g = int(T[x][g])
    return g

while len(front) and len(rels) < NREL:
    nxt = []
    for x in (1, 2, -1, -2):
        tgt = T[x][front]
        fresh = dep[tgt] < 0
        # first discovery of each fresh target (np.unique keeps first occurrence)
        ft, idx = np.unique(tgt[fresh], return_index=True)
        src = front[fresh][idx]
        par[ft] = src; plet[ft] = x; dep[ft] = dep[src] + 1
        nxt.append(ft)
        # non-tree edges out of this layer give relators
        for g, h in zip(front[~fresh][:20000], tgt[~fresh][:20000]):
            if par[h] == g and plet[h] == x: continue
            r = reduce(word(int(g)) + [x] + [-y for y in word(int(h))[::-1]])
            if not r: continue
            c = canon(r)
            if c in seen: continue
            seen.add(c); rels.append(r)
            if len(rels) >= NREL: break
        if len(rels) >= NREL: break
    front = np.unique(np.concatenate(nxt)) if nxt else np.array([], np.int64)

name = {1: 'b', 2: 'd', -1: 'b^-1', -2: 'd^-1'}
def pqword(w):
    out = []; i = 0
    while i < len(w):
        j = i
        while j < len(w) and w[j] == w[i]: j += 1
        g = 'b' if abs(w[i]) == 1 else 'd'; k = (j - i) * (1 if w[i] > 0 else -1)
        out.append(g if k == 1 else '%s^%d' % (g, k)); i = j
    return '*'.join(out)
q = 2 ** e // 4   # b, d have order m/4 in Bbar_e; checked here on the tables
rels = [[1] * q, [2] * q] + rels
for r in rels:
    assert evaluate(r) == 0
    print(pqword(r))
sys.stderr.write('e=%d |Bbar|=%d relators=%d max length=%d\n' % (e, N, len(rels), max(len(r) for r in rels)))
