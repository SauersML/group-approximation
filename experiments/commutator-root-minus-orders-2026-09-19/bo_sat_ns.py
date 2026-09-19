"""Finite-ball consistency test for a bi-order on N (normal closure of y) in G(K; al, be), with a choice of how t
(the index shift y_i -> y_{i+1}) acts on the order.  Ball B = nonempty freely reduced words of length <= r in
y_0..y_{W-1}, merged into classes by exact equality (tower_wp).  One boolean per class ("g > 1").  Clauses (all
verified exactly):  g xor g^-1;  g, h > 1 => gh > 1 (when gh is in B);  g > 1 <=> s^-1 g s > 1 (s a letter);
and, by SHIFT:  1: g <=> shift(g) (t-invariant order, i.e. a bi-order of G);  -1: g <=> not shift(g)
(t-reversing order; it is t^2-invariant, so it bi-orders G_2 = N x| <t^2> lexicographically);  0: no shift
clause (an arbitrary bi-order of N_[0,W-1]).
Candidate identities are found via images in finite quotients (perms file) and then checked exactly.
UNSAT = certificate that no order of the chosen kind exists (each clause is a necessary consequence).
SAT = only consistency on the ball, not an order.
usage: bo_sat_ns.py K al be permsfile W r nreps SHIFT
"""
import sys, itertools
import numpy as np
from tower_wp import Tower, inv, free_reduce
from pysat.solvers import Cadical153

K, al, be = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
permsfile, W, r = sys.argv[4], int(sys.argv[5]), int(sys.argv[6])
nreps = int(sys.argv[7]) if len(sys.argv) > 7 else 24
SHIFT = int(sys.argv[8]) if len(sys.argv) > 8 else 1
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

# global permutation of y_i (i in -1..W) : right action, y_i = t^-i y t^i
def gperm(i, e):
    out = np.empty(D, dtype=np.int64)
    for k, (Y, T) in enumerate(reps):
        # compute t^-i y t^i as composition applied left to right
        P = np.arange(len(Y))
        Tinv = pinv(T)
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

words = []
frontier = [()]
for L in range(1, r + 1):
    nf = []
    for w in frontier:
        for s in letters:
            if w and w[-1][0] == s[0] and w[-1][1] == -s[1]:
                continue
            nf.append(w + (s,))
    words += nf
    frontier = nf
M = np.empty((len(words), D), dtype=np.int64)
for n, w in enumerate(words):
    p = np.arange(D)
    for s in w:
        p = G[s][p]
    M[n] = p
rng = np.random.default_rng(7)
Wt = rng.integers(1, 2**62, size=D, dtype=np.uint64)
def keys(rows):
    return (rows.astype(np.uint64) * Wt).sum(axis=1)
idkey = keys(np.arange(D)[None, :])[0]
T = Tower(K, al, be)
eq = lambda u, v: T.trivial_N(u + inv(v))
# classes
wkeys = keys(M)
cls, reps_w, rep_row, bykey = {}, [], [], {}
for n, w in enumerate(words):
    k = int(wkeys[n])
    if k == int(idkey) and T.trivial_N(w):
        cls[w] = None
        continue
    for c in bykey.get(k, []):
        if eq(w, reps_w[c]):
            cls[w] = c
            break
    else:
        c = len(reps_w)
        reps_w.append(w); rep_row.append(n)
        bykey.setdefault(k, []).append(c)
        cls[w] = c
C = len(reps_w)
print('words', len(words), 'classes', C, 'trivial', sum(v is None for v in cls.values()), flush=True)
var = lambda c: c + 1
clauses = []
for c, w in enumerate(reps_w):
    ci = cls[inv(w)]
    if ci < c:
        continue
    clauses += [[var(c), var(ci)], [-var(c), -var(ci)]]
def lookup(k, word):
    for c in bykey.get(k, []):
        if eq(word, reps_w[c]):
            return c
    return None
# shift
for c, w in enumerate(reps_w if SHIFT in (1, -1) else []):
    if max(i for i, _ in w) < W - 1:
        d = cls[tuple((i + 1, e) for i, e in w)]
        if d is not None and d != c:
            if SHIFT == 1: clauses += [[-var(c), var(d)], [var(c), -var(d)]]
            else: clauses += [[-var(c), -var(d)], [var(c), var(d)]]
# conjugation by letters
for c, w in enumerate(reps_w):
    for s in letters:
        u = free_reduce(((s[0], -s[1]),) + w + (s,))
        if u in cls:
            d = cls[u]
        else:
            row = G[s][M[rep_row[c]][G[(s[0], -s[1])]]]
            d = lookup(int(keys(row[None, :])[0]), u)
        if d is not None and d != c:
            clauses.append([-var(c), var(d)])
nprod = 0
Mr = M[rep_row]
sk = sorted(bykey)
skarr = np.array(sk, dtype=np.uint64)
for c in range(C):
    prod = Mr[:, Mr[c]]  # row h: image of g_c * g_h
    kk = keys(prod)
    pos = np.searchsorted(skarr, kk)
    pos[pos >= len(skarr)] = 0
    hit = np.nonzero(skarr[pos] == kk)[0]
    for h in map(int, hit):
        u = free_reduce(reps_w[c] + reps_w[h])
        d = cls.get(u, -1) if len(u) <= r and all(i < W for i, _ in u) else -1
        if d == -1:
            d = lookup(int(kk[h]), u)
        if d is not None and d not in (c, h):
            clauses.append([-var(c), -var(h), var(d)]); nprod += 1
print('clauses', len(clauses), 'product clauses', nprod, flush=True)
s = Cadical153(bootstrap_with=clauses)
res = s.solve()
print('K al be', K, al, be, 'W', W, 'r', r, 'SAT' if res else 'UNSAT', flush=True)
if res:
    m = s.get_model()
    pos = [reps_w[c] for c in range(C) if m[c] > 0 and len(reps_w[c]) == 1]
    print('positive letters', pos)
