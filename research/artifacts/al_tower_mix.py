#!/usr/bin/env python3
"""Minimal Atkin--Lehner mismatch of MIXTURES of vertex-orbit representations.
Group G' = Gamma_0(p^{2k}) mod p^{4k}, depth k (default 1).  Pieces: the spheres
S(o,2j) = P^1(Z/p^{2j}) for j = k..J (as Gamma_0(p^{2k})-sets, Moebius action) and
their Ad(g_k)-twists.  We compute, for each piece, its isotypic weight vector over
the common isotypic decomposition of V = (+) pieces, then minimise
TV(sum_j w_j mu_j, sum_j w_j mu_j^twist) over probability vectors w (grid).
Pieces at level 2j > 2k need the group mod p^{2J} to act; we use G'' = Gamma_0(p^{2k})
mod p^{max(4k,2J+2k)} so both actions are defined."""
import sys, itertools, numpy as np
from collections import deque
p = int(sys.argv[1]) if len(sys.argv) > 1 else 2
k = int(sys.argv[2]) if len(sys.argv) > 2 else 1
J = int(sys.argv[3]) if len(sys.argv) > 3 else 3
MOD = p**max(4*k, 2*J + 2*k)
N2k = p**(2*k)

def units_generators(p, m):
    if p == 2: return [(-1) % 2**m, 5 % 2**m]
    n = p**m; phi = (p-1)*p**(m-1)
    fac = [q for q in range(2, phi+1) if phi % q == 0 and all(q % r for r in range(2, int(q**0.5)+1))]
    for g in range(2, n):
        if g % p == 0: continue
        if all(pow(g, phi//q, n) != 1 for q in fac): return [g]
gens = [((1,1),(0,1)), ((1,0),(N2k % MOD, 1))]
for u in units_generators(p, 2*k):
    uu = u % MOD; gens.append(((uu,0),(0,pow(uu,-1,MOD))))

def sphere(j):
    n = p**(2*j)
    return [(x % n, 1) for x in range(n)] + [(1, (p*y) % n) for y in range(p**(2*j-1))]
def normalize(v, n):
    x, y = v[0] % n, v[1] % n
    if y % p != 0: return ((x*pow(y,-1,n)) % n, 1)
    return (1, (y*pow(x,-1,n)) % n)
def act(M, v, j, twisted):
    n = p**(2*j); (a,b),(c,d) = M
    if twisted:
        cq = (c // N2k) % n; a,b,c,d = d % n, (-cq) % n, 0, a % n
    x,y = v; return normalize((a*x+b*y, c*x+d*y), n)

pieces = []   # (label, points, twisted)
for j in range(k, J+1):
    pieces.append((f"S{2*j}", sphere(j), False)); pieces.append((f"S{2*j}^g", sphere(j), True))
offs = []; n = 0
for lab, pts, tw in pieces: offs.append(n); n += len(pts)
perms = []
for M in gens:
    perm = np.zeros(n, dtype=int)
    for (lab, pts, tw), o in zip(pieces, offs):
        idx = {pt:i for i,pt in enumerate(pts)}
        for i, pt in enumerate(pts): perm[o+i] = o + idx[act(M, pt, int(lab[1:].rstrip('^g'))//2, tw)]
    perms.append(perm)
# orbital algebra
seen = -np.ones((n,n), dtype=np.int64); orbs = []
for i in range(n):
    for jj in range(n):
        if seen[i,jj] >= 0: continue
        oid = len(orbs); seen[i,jj] = oid; q = deque([(i,jj)]); mem = [(i,jj)]
        while q:
            u,v = q.popleft()
            for s in perms:
                a,b = s[u], s[v]
                if seen[a,b] < 0: seen[a,b] = oid; q.append((a,b)); mem.append((a,b))
        orbs.append(mem)
m = len(orbs); print(f"p={p} k={k} J={J} n={n} orbitals={m}", flush=True)
rng = np.random.default_rng(0)
A = np.zeros((n,n))
for mem in orbs:
    cc = rng.standard_normal()
    for (u,v) in mem: A[u,v] += cc
A = (A + A.T)/2
w, U = np.linalg.eigh(A)
blocks = []; i = 0
while i < n:
    jj = i
    while jj+1 < n and abs(w[jj+1]-w[i]) < 1e-7*max(1.0,abs(w[i])): jj += 1
    blocks.append((i,jj+1)); i = jj+1
nb = len(blocks); adj = np.zeros((nb,nb), dtype=bool)
Ub = [U[:, a:b] for (a,b) in blocks]
for mem in orbs:
    O = np.zeros((n,n))
    for (u,v) in mem: O[u,v] = 1.0
    T = U.T @ O @ U
    for r,(a,b) in enumerate(blocks):
        row = T[a:b]
        for t,(c,d) in enumerate(blocks):
            if r != t and not adj[r,t] and np.abs(row[:, c:d]).max() > 1e-8: adj[r,t] = adj[t,r] = True
comp = -np.ones(nb, dtype=int); cid = 0
for r in range(nb):
    if comp[r] >= 0: continue
    st = [r]; comp[r] = cid
    while st:
        x = st.pop()
        for y in np.nonzero(adj[x])[0]:
            if comp[y] < 0: comp[y] = cid; st.append(y)
    cid += 1
projs = []
for c in range(cid):
    cols = np.concatenate([np.arange(a,b) for r,(a,b) in enumerate(blocks) if comp[r]==c])
    projs.append(U[:, cols])
print(f"isotypic components: {cid}", flush=True)
# weight vectors per piece
W = {}
for (lab, pts, tw), o in zip(pieces, offs):
    sz = len(pts); vec = np.zeros(cid)
    for c, Uc in enumerate(projs):
        vec[c] = np.sum(Uc[o:o+sz, :]**2) / sz
    W[lab] = vec
levels = [f"S{2*j}" for j in range(k, J+1)]
def tv(wts):
    mu = sum(wt*W[l] for wt, l in zip(wts, levels)); nu = sum(wt*W[l+"^g"] for wt, l in zip(wts, levels))
    return np.abs(mu-nu).sum()
for l in levels: print(f"  single level {l}: TV = {tv([1.0 if x==l else 0.0 for x in levels]):.6f}")
best = (9, None); G = 40
for comb in itertools.product(range(G+1), repeat=len(levels)):
    if sum(comb) != G: continue
    wts = [c/G for c in comb]; t = tv(wts)
    if t < best[0]: best = (t, wts)
print(f"  min TV over mixtures (grid {G}): {best[0]:.6f} at weights {best[1]}", flush=True)
