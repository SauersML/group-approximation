"""Relative step for e >= 9: the defects beta'' = beta^R beta^-1 over all of Bbar_e, and the smallest
subgroup Bbar_0 with M = <<R>>_(Q_B) <= A.Bbar_0 (A.Bbar_0 a subgroup of Q_B).

Input: ck<e>/L<K>.npz and ck<e>/L<K-1>.npz from levels_ck.py with |G_K| = |G_(K-1)| (stable, so
G_K = Bbar_e by the stabilization lemma and pi: G_K -> G_(K-1) is an isomorphism).
Group elements are ids of G_K. Model section of g at the letter x: pi^-1(h_(x mod M)).
True section after one letter = swap(model section), swap = sigma^2 (b <-> d); along R (8 letters)
no swap. Products x*y are evaluated by right-multiplying x along a b,d-word of y (BFS tree).
Facts used (w13, section 3):
  * A.Bbar_0 is a subgroup of Q_B iff Bbar_0 is closed under true one-letter sections;
  * then M <= A.Bbar_0 iff every beta'' lies in Bbar_0 (beta R beta^-1 = S_beta beta'').
usage: python3 rel.py e K
"""
import sys, os
import numpy as np
e = int(sys.argv[1]); K = int(sys.argv[2])
m = 2 ** e; n = m // 4; M = max(2 ** (e - 4), 2)
z1 = np.load('ck%d/L%d.npz' % (e, K)); z0 = np.load('ck%d/L%d.npz' % (e, K - 1))
Rb, Rd, rows, pi = z1['Rb'], z1['Rd'], z1['rows'], z1['pi']
N = len(Rb); assert N == len(z0['Rb']), "levels K-1, K not stable"
assert len(np.unique(pi)) == N
pinv = np.empty(N, dtype=np.int32); pinv[pi] = np.arange(N, dtype=np.int32)
GEN = [Rb, Rd]
print("e=%d K=%d |Bbar| = %d = 2^%d" % (e, K, N, int(np.log2(N))), flush=True)
# exact verification of the hash-based BFS: rows are pairwise distinct, and the tables Rb, Rd agree
# exactly with the recursion  g o b = (s, r -> h_r o d^(3^r)),  g o d = (s+1, r -> h_(Tr) o b)
# evaluated with the level K-1 tables. Then rows = G_K exactly (a set closed under o b, o d).
T = pow(3, -1, m); pw = [pow(3, r, n) for r in range(M)]; Tr = [(T * r) % M for r in range(M)]
Rb0, Rd0 = z0['Rb'], z0['Rd']
def dpow(v):
    out = np.arange(len(Rd0)); P = Rd0.copy()
    while v:
        if v & 1: out = P[out]
        v >>= 1
        if v: P = P[P]
    return out
Dv = {v: dpow(v) for v in set(pw)}
ok = (rows[Rb, 0] == rows[:, 0]).all() and (rows[Rd, 0] == (rows[:, 0] + 1) % n).all()
for r in range(M):
    ok &= bool((rows[Rb, 1 + r] == Dv[pw[r]][rows[:, 1 + r]]).all())
    ok &= bool((rows[Rd, 1 + r] == Rb0[rows[:, 1 + Tr[r]]]).all())
srt = np.lexsort(rows.T[::-1]); dif = (rows[srt[1:]] != rows[srt[:-1]]).any(axis=1)
ok &= bool(dif.all()); del srt, dif
assert ok, "exact verification failed"
print("exact verification of rows and tables: OK", flush=True)

# BFS tree from 1: parent, generator (0=b, 1=d), and the swap automorphism b <-> d
parent = -np.ones(N, dtype=np.int32); gen = -np.ones(N, dtype=np.int8)
swap = -np.ones(N, dtype=np.int32); parent[0] = 0; swap[0] = 0
front = np.array([0]); depth = 0
while len(front):
    nxt = []
    for gi, R in enumerate(GEN):
        c = R[front]; fresh = parent[c] < 0
        c, idx = np.unique(c[fresh], return_index=True); src = front[fresh][idx]
        fresh2 = parent[c] < 0; c, src = c[fresh2], src[fresh2]
        parent[c] = src; gen[c] = gi; swap[c] = GEN[1 - gi][swap[src]]; nxt.append(c)
    front = np.concatenate(nxt); depth += 1
assert (parent >= 0).all()
gen[0] = -1
# check swap is an automorphism: swap(g b) = swap(g) d, swap(g d) = swap(g) b
assert (swap[Rb] == Rd[swap]).all() and (swap[Rd] == Rb[swap]).all()
print("BFS radius", depth - 1, flush=True)

def prod(x, y, chunk=1 << 18):
    x = np.asarray(x, dtype=np.int32); y = np.asarray(y, dtype=np.int32); out = np.empty_like(x)
    for s in range(0, len(x), chunk):
        cx = x[s:s + chunk].copy(); cy = y[s:s + chunk].copy(); gens = []
        while (cy != 0).any():
            gens.append(np.where(cy != 0, gen[cy], -1)); cy = parent[cy]
        for g in reversed(gens):
            for gi, R in enumerate(GEN):
                mk = g == gi; cx[mk] = R[cx[mk]]
        out[s:s + chunk] = cx
    return out

# inverse: inv(g x) = x^-1 inv(g); via left multiplication tables L_b, L_d (L_x(g y) = L_x(g) y)
def lefttab(xel):
    L = -np.ones(N, dtype=np.int32); L[0] = xel
    fr = np.array([0])
    while len(fr):
        nx = []
        for R in GEN:
            c = R[fr]; v = R[L[fr]]; f = L[c] < 0; L[c[f]] = v[f]; nx.append(c[f])
        fr = np.unique(np.concatenate(nx))
    return L
Lb, Ld = lefttab(Rb[0]), lefttab(Rd[0])
Lbi = np.empty(N, dtype=np.int32); Lbi[Lb] = np.arange(N); Ldi = np.empty(N, dtype=np.int32); Ldi[Ld] = np.arange(N)
inv = -np.ones(N, dtype=np.int32); inv[0] = 0; fr = np.array([0])
while len(fr):
    nx = []
    for R, Li in ((Rb, Lbi), (Rd, Ldi)):
        c = R[fr]; v = Li[inv[fr]]; f = inv[c] < 0; inv[c[f]] = v[f]; nx.append(c[f])
    fr = np.unique(np.concatenate(nx))
assert (prod(np.arange(N), inv) == 0).all()

def order(g):
    p, x = 1, g
    while x != 0: x = prod([x], [g])[0]; p += 1
    return p
def power(g, k):
    x = 0
    for _ in range(k): x = prod([x], [g])[0]
    return x
b, d = int(Rb[0]), int(Rd[0])
ob = 1; x = b
while x != 0: x = int(Rb[x]); ob += 1
print("ord b = %d, ord(b d) = %d" % (ob, order(int(Rd[b]))), flush=True)

def msec(g, x): return pinv[rows[g, 1 + (x % M)]]
Rw = [(-1) % m, (-1) % m, 1, 1, (-1) % m, (-1) % m, 1, 1]
allg = np.arange(N, dtype=np.int32); gR = allg.copy()
for x in Rw: gR = msec(gR, x)
dd = prod(gR, inv)                         # beta'' = beta^R beta^-1
vals, cnt = np.unique(dd, return_counts=True)
print("beta'' != 1 for %d of %d beta; %d distinct values" % ((dd != 0).sum(), N, len(vals)), flush=True)
bp = {}; x = 0
for j in range(ob): bp[x] = j; x = int(Rb[x])
dp = {}; x = 0
for j in range(ob): dp[x] = j; x = int(Rd[x])
for v, c in zip(vals[:40], cnt[:40]):
    lab = ('b^%d' % bp[v]) if v in bp else (('d^%d' % dp[v]) if v in dp else 'other(depth-word)')
    print("  beta'' value %d (%s): %d times" % (v, lab, c))
bd = int(Rd[b]); print("(b d)'' =", dd[bd], "= b^%s" % bp.get(int(dd[bd]), '?'), flush=True)
np.save('ck%d/defects.npy' % e, dd)

def closure(gens):
    """subgroup generated by gens (list of ids), by right multiplication."""
    S = np.zeros(N, dtype=bool); S[0] = True; fr = np.array([0], dtype=np.int32)
    while len(fr):
        nx = []
        for g in gens:
            c = prod(fr, np.full(len(fr), g, dtype=np.int32)); c = c[~S[c]]; c = np.unique(c); S[c] = True; nx.append(c)
        fr = np.concatenate(nx) if nx else np.zeros(0, dtype=np.int32)
    return S
def is_central(g):
    return bool(prod([g], [b])[0] == prod([b], [g])[0] and prod([g], [d])[0] == prod([d], [g])[0])
def sec_closed_hull(gens):
    """smallest subgroup containing gens, closed under swap and under model one-letter sections
    (hence under true sections at a-letters, swap o msec, and at c-letters)."""
    gens = list(dict.fromkeys(int(g) for g in gens))
    while True:
        S = closure(gens); els = np.nonzero(S)[0].astype(np.int32)
        new = set()
        for x in range(M):
            t = msec(els, x); new.update(int(u) for u in np.unique(t[~S[t]]))
        t = swap[els]; new.update(int(u) for u in np.unique(t[~S[t]]))
        if not new: return S, gens
        gens += sorted(new)[:8]
nz = [int(v) for v in vals if v != 0]
print("central defects:", sum(is_central(v) for v in nz), "of", len(nz), flush=True)
S0, g0 = sec_closed_hull(nz)
print("smallest section-closed Bbar_0 containing all beta'': order %d, index %d" % (S0.sum(), N // S0.sum()), flush=True)
b64, d64 = power(b, 64), power(d, 64)
S1 = closure([b64, d64])
print("<b^64, d^64>: order %d, contains all beta'': %s, b^64 central: %s" % (S1.sum(), bool(S1[dd].all()), is_central(b64)), flush=True)
t = np.concatenate([msec(np.nonzero(S1)[0], x) for x in range(M)] + [swap[np.nonzero(S1)[0]]])
print("<b^64, d^64> closed under swap and sections:", bool(S1[t].all()), flush=True)
