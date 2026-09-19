"""Relators of level k of the B-tree closed form found by breadth-first search on the positive Cayley
graph (generators b, d) from the identity, elements evaluated recursively by evalk.mul (no tables).
Each coincidence g x = h gives the relator w(g) x w(h)^-1.  Relators are re-checked by evalk.trivial.
usage: python3 ballk.py e k NREL MAXBALL > rels.txt
"""
import sys
import numpy as np
e, k, NREL, MAXBALL = (int(x) for x in sys.argv[1:5])
sys.argv = [sys.argv[0], str(e), str(k)]
import evalk as E
M = E.M; n = E.n
def flat(A):
    B = A[0].shape[0]
    return np.concatenate([a.reshape(B, -1) for a in A], axis=1).astype(np.int16)
A0 = [np.zeros((1,) + (M,) * i, np.int64) for i in range(k)]
seen = {flat(A0)[0].tobytes(): 0}
par = [0]; let = [0]; fid = [0]; front = A0
def word(i):
    w = []
    while i: w.append(let[i]); i = par[i]
    return w[::-1]
rels = []; cset = set()
while len(fid) and len(rels) < NREL and len(par) < MAXBALL:
    nf, nid = [], []
    for x, g in ((1, 'b'), (2, 'd')):
        G = E.mul(front, g, np.ones(len(fid), np.int64)); F = flat(G)
        for j in range(len(fid)):
            key = F[j].tobytes()
            if key in seen:
                h = seen[key]
                if par[h] == fid[j] and let[h] == x: continue
                a, b = word(fid[j]) + [x], word(h)
                while a and b and a[0] == b[0]: a, b = a[1:], b[1:]
                c = (tuple(a), tuple(b))
                if (a or b) and c not in cset and len(rels) < NREL:
                    cset.add(c); rels.append((a, b))
            else:
                seen[key] = len(par); par.append(fid[j]); let.append(x)
                nf.append([a_[j] for a_ in G]); nid.append(len(par) - 1)
    fid = nid
    front = [np.stack([t[i] for t in nf]) for i in range(k)] if nf else []
    sys.stderr.write('layer: |ball|=%d front=%d rels=%d\n' % (len(par), len(fid), len(rels)))
def pqword(a, b):
    w = a + [-y for y in b[::-1]]
    out = []; i = 0
    while i < len(w):
        j = i
        while j < len(w) and w[j] == w[i]: j += 1
        g = 'b' if abs(w[i]) == 1 else 'd'; kk = (j - i) * (1 if w[i] > 0 else -1)
        out.append(g if kk == 1 else '%s^%d' % (g, kk)); i = j
    return '*'.join(out)
lines = ['b^%d' % n, 'd^%d' % n] + [pqword(a, b) for a, b in rels]
for L in lines:
    assert E.trivial(E.parse(L)), L
    print(L)
sys.stderr.write('e=%d level %d ball=%d relators=%d max length=%d\n' % (e, k, len(par), len(lines), max(len(a) + len(b) for a, b in rels)))
