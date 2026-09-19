"""Finite-ball SAT test for bi-invariant total PREORDERS on G(K; al, be) = <y, t | y_1^K = [y_0^al, y_2^be]>
with y strictly positive.  Such a preorder exists iff some bi-orderable group Q receives a map phi: G -> Q with
phi(y) != 1 (the preorder is g >= 1 <=> phi(g) >= 1; conversely P = {g >= 1} gives Q = G / (P cap P^-1)).
So UNSAT on a ball proves: every map from G to a bi-orderable group kills y (a class-killing obstruction for all
bi-orderable targets, not just a statement about G).  With --inj the test is for bi-orders of G itself.

Ball B = reduced words of length <= r in y_0..y_{W-1}, merged into classes by exact equality in G (Britton's
lemma, tower_wp.py; finite quotients only propose candidate coincidences, every identity used is checked exactly).
One boolean p(g) = [g >= 1] per class.  Clauses, each a necessary condition:
  (T) p(g) or p(g^-1)                        [--inj adds: not both]
  (M) p(g) and p(h) => p(gh)   for |g| <= r1 (either order of the product), whenever gh is in B
  (C) p(g) => p(s^-1 g s)      for every letter s
  (S) p(g) <=> p(shift g)      (conjugation by t)
  (Y) not p(y_0^-1)            (y > 1 strictly, after possibly reversing the order)
  --chain (only for al = be = 1, K > 0): not p(y_i^k y_{i+1}^-1), k < r, i.e. y_i^k < y_{i+1}; this is forced by
          item 4 of commutator-root-frontier-kills-pl-and-bi-ordered-targets (the convex classes increase).
usage: pre_sat.py K al be permsfile W r r1 [--inj] [--chain] [--nreps N]
"""
import sys, os, time
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'commutator-root-orders-2026-09-18'))
from tower_wp import Tower, inv, free_reduce
from pysat.solvers import Cadical153

args = [a for a in sys.argv[1:] if not a.startswith('--')]
INJ, CHAIN = '--inj' in sys.argv, '--chain' in sys.argv
nreps = 24
if '--nreps' in sys.argv:
    nreps = int(sys.argv[sys.argv.index('--nreps') + 1]); args.remove(str(nreps))
K, al, be = int(args[0]), int(args[1]), int(args[2])
permsfile, W, r, r1 = args[3], int(args[4]), int(args[5]), int(args[6])
t0 = time.time()
reps = []
for line in open(permsfile):
    rest = line.split(' ', 1)[1].strip().rsplit(' ', 1)[0]
    a, b = rest.split('] [')
    reps.append((np.array([int(x) - 1 for x in a.strip('[] ').split(',')]),
                 np.array([int(x) - 1 for x in b.strip('[] ').split(',')])))
reps.sort(key=lambda p: -len(p[0]))
reps = reps[:nreps]
offs = np.cumsum([0] + [len(p[0]) for p in reps])
D = int(offs[-1])


def pinv(p):
    q = np.empty_like(p); q[p] = np.arange(len(p)); return q


def gperm(i, e):  # image of y_i^e = t^-i y^e t^i, right action (same convention as bo_sat.py)
    out = np.empty(D, dtype=np.int32)
    for k, (Y, T) in enumerate(reps):
        P = np.arange(len(Y)); Tinv = pinv(T)
        for _ in range(i):
            P = Tinv[P]
        P = Y[P]
        for _ in range(i):
            P = T[P]
        if e == -1:
            P = pinv(P)
        out[offs[k]:offs[k + 1]] = P + offs[k]
    return out


G = {(i, e): gperm(i, e) for i in range(W) for e in (1, -1)}
letters = sorted(G)
words, rows = [], []
frontier, frows = [()], [np.arange(D, dtype=np.int32)]
for L in range(1, r + 1):
    nf, nr = [], []
    for w, p in zip(frontier, frows):
        for s in letters:
            if w and w[-1][0] == s[0] and w[-1][1] == -s[1]:
                continue
            nf.append(w + (s,)); nr.append(G[s][p])
    words += nf; rows += nr
    frontier, frows = nf, nr
M = np.array(rows, dtype=np.int32); del rows, frows
rng = np.random.default_rng(7)
Wt = rng.integers(1, 2**62, size=D, dtype=np.uint64)
keys = lambda R: (R.astype(np.uint64) * Wt).sum(axis=1)
idkey = int(keys(np.arange(D)[None, :])[0])
T = Tower(K, al, be)
eq = lambda u, v: T.trivial_N(u + inv(v))
wkeys = keys(M)
cls, reps_w, rep_row, bykey = {}, [], [], {}
for n, w in enumerate(words):
    k = int(wkeys[n])
    if k == idkey and T.trivial_N(w):
        cls[w] = None; continue
    for c in bykey.get(k, []):
        if eq(w, reps_w[c]):
            cls[w] = c; break
    else:
        c = len(reps_w); reps_w.append(w); rep_row.append(n)
        bykey.setdefault(k, []).append(c); cls[w] = c
C = len(reps_w)
print('K al be', K, al, be, 'W', W, 'r', r, 'r1', r1, 'inj' if INJ else 'pre', 'chain' if CHAIN else '',
      '| words', len(words), 'classes', C, 'trivial', sum(v is None for v in cls.values()),
      'D', D, '%.0fs' % (time.time() - t0), flush=True)
inwin = lambda u: len(u) <= r and all(0 <= i < W for i, _ in u)


def find(u, k):
    """class of the reduced word u (key k), None if trivial, -1 if not in the ball."""
    if inwin(u):
        return cls[u] if u else None
    if not u:
        return None
    for c in bykey.get(k, []):
        if eq(u, reps_w[c]):
            return c
    if k == idkey and T.trivial_N(u):
        return None
    return -1


var = lambda c: c + 1
clauses, stats = [], dict(T=0, M=0, C=0, S=0)
for c, w in enumerate(reps_w):
    ci = cls[inv(w)]
    if ci < c:
        continue
    clauses.append([var(c), var(ci)]); stats['T'] += 1
    if INJ:
        clauses.append([-var(c), -var(ci)])
for c, w in enumerate(reps_w):
    if max(i for i, _ in w) < W - 1:
        d = cls[tuple((i + 1, e) for i, e in w)]
        if d is not None and d != c:
            clauses += [[-var(c), var(d)], [var(c), -var(d)]]; stats['S'] += 1
Mr = M[rep_row]; del M
for c, w in enumerate(reps_w):
    for s in letters:
        u = free_reduce(((s[0], -s[1]),) + w + (s,))
        row = G[s][Mr[c][G[(s[0], -s[1])]]]
        d = find(u, int(keys(row[None, :])[0]))
        if d not in (None, -1, c):
            clauses.append([-var(c), var(d)]); stats['C'] += 1
skarr = np.array(sorted(bykey), dtype=np.uint64)
short = [c for c, w in enumerate(reps_w) if len(w) <= r1]
seen = set()
for c in short:
    Mg = Mr[c]
    for side in (0, 1):
        prod = Mr[:, Mg] if side == 0 else Mg[Mr]  # side 0: g_c * g_h ; side 1: g_h * g_c
        kk = keys(prod)
        pos = np.searchsorted(skarr, kk); pos[pos >= len(skarr)] = 0
        for h in map(int, np.nonzero(skarr[pos] == kk)[0]):
            u = free_reduce(reps_w[c] + reps_w[h] if side == 0 else reps_w[h] + reps_w[c])
            d = find(u, int(kk[h]))
            if d in (None, -1, c, h):
                continue
            cl = (min(c, h), max(c, h), d)
            if cl not in seen:
                seen.add(cl); clauses.append([-var(c), -var(h), var(d)]); stats['M'] += 1
y0inv = cls[((0, -1),)]
clauses.append([-var(y0inv)])
nchain = 0
if CHAIN:
    for i in range(W - 1):
        for k in range(1, r):
            u = ((i, 1),) * k + ((i + 1, -1),)
            if cls.get(u) is not None:
                clauses.append([-var(cls[u])]); nchain += 1
print('clauses', len(clauses), stats, 'chain units', nchain, '%.0fs' % (time.time() - t0), flush=True)
s = Cadical153(bootstrap_with=clauses)
res = s.solve()
print('RESULT K al be', K, al, be, 'W', W, 'r', r, 'r1', r1, 'inj' if INJ else 'pre', 'chain' if CHAIN else '',
      'SAT' if res else 'UNSAT', '%.0fs' % (time.time() - t0), flush=True)
if res:
    m = s.get_model()
    kern = [reps_w[c] for c in range(C) if m[c] > 0 and m[cls[inv(reps_w[c])]] > 0 and len(reps_w[c]) <= 2]
    print('kernel elements of length <= 2 in the model:', kern[:20])
