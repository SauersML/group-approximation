#!/usr/bin/env python3
"""Turning-face search for the diagonal link X_n of |NCP_n| with ALL opposite universal pairs.

Usage: python3 nc_pairs.py n [--witness K]

Conventions (see notes/zaremsky-3-06-braid-groups-cat0-frontier-swarm-2026-09-16.md):
  points 0..n-1 on a circle; a partition is a tuple of non-singleton block bitmasks (sorted);
  rank = n - #blocks (singletons counted).
  I   : {1..n-2} minus rk(F) contains two consecutive integers
  II  : some vertex of F is not universal (universal = exactly one block, a cyclic interval)
  III': some gap of F contains two partitions failing modularity in S(V)
  pairs: pi = (p, c), p in Z/n, 1 <= c <= n-2, arcs A1 = {p+1..p+c}, A2 = {p+c+1..p+n-1},
         v = block A1+{p}, w = block A2+{p}; opposite universal vertices of the building.
  compat(P, pi): every block of P not containing p lies inside A1 or inside A2
         (<=> f(P) = (f(P) cap f(v)) + (f(P) cap f(w)) <=> P, v, w lie in a common apartment of B).
  IV_adj(F): exists maximal chain C with no ADJACENT pair (c in {1, n-2}) compatible with F and C
         (this is condition IV of research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md)
  IV_all(F): same with all n(n-2) pairs.
"""
import sys, itertools
import numpy as np

n = int(sys.argv[1])
FULL = (1 << n) - 1
popc = lambda m: bin(m).count("1")

# ---------- set partitions and noncrossing ones ----------
def set_partitions(n):
    def rec(i, blocks):
        if i == n:
            yield blocks
            return
        for k in range(len(blocks)):
            nb = list(blocks); nb[k] = nb[k] | (1 << i)
            yield from rec(i + 1, nb)
        yield from rec(i + 1, blocks + [1 << i])
    yield from rec(0, [])

def canon(blocks):
    return tuple(sorted(b for b in blocks if popc(b) >= 2))

def elems(m):
    return [i for i in range(n) if m >> i & 1]

def crossing_pair(b1, b2):
    e = elems(b1)
    k = len(e)
    for j in range(k):
        a, c = e[j], e[(j + 1) % k]
        if j < k - 1:
            gap = sum(1 << t for t in range(a + 1, c))
        else:
            gap = sum(1 << t for t in range(a + 1, n)) | sum(1 << t for t in range(0, c))
        if b2 & ~gap == 0:
            return False
    return True

def is_noncrossing(bl):
    return all(not crossing_pair(bl[i], bl[j]) for i in range(len(bl)) for j in range(i + 1, len(bl)))

allparts = set(canon(p) for p in set_partitions(n))
NC = sorted((p for p in allparts if is_noncrossing(p)), key=lambda p: (sum(popc(b) - 1 for b in p), p))
N = len(NC)
idx = {p: i for i, p in enumerate(NC)}
rank = [sum(popc(b) - 1 for b in p) for p in NC]
ZERO = idx[()]
ONE = idx[(FULL,)]

def leq_p(x, y):  # x refines y
    return all(any(bx & by == bx for by in y) for bx in x)

leq = np.zeros((N, N), dtype=bool)
for i, x in enumerate(NC):
    for j, y in enumerate(NC):
        if rank[i] <= rank[j] and leq_p(x, y):
            leq[i, j] = True

def join_full(x, y):
    blocks = list(x)
    for by in y:
        merged = by; keep = []
        for b in blocks:
            if b & merged:
                merged |= b
            else:
                keep.append(b)
        blocks = keep + [merged]
    return canon(blocks)

def nblocks(p):
    return n - sum(popc(b) - 1 for b in p)

def meet(x, y):
    return canon([bx & by for bx in x for by in y])

def fail_mod(i, j):
    x, y = NC[i], NC[j]
    jp = join_full(x, y)
    if jp not in idx:
        return True
    return nblocks(x) + nblocks(y) - nblocks(jp) != nblocks(meet(x, y))

# ---------- gap table G[a,b]: open interval (a,b) contains a failing pair ----------
S = np.zeros((N, N), dtype=np.float32)
nfail = 0
for i in range(N):
    for j in range(i + 1, N):
        if leq[i, j] or leq[j, i]:
            continue
        if fail_mod(i, j):
            nfail += 1
            m = idx[meet(NC[i], NC[j])]
            ub = np.nonzero(leq[i] & leq[j])[0]
            jn = min(ub, key=lambda t: rank[t])
            S[m, jn] = 1.0
L = leq.astype(np.float32)
H2 = (S @ L) > 0
G = (L @ H2.astype(np.float32)) > 0

# ---------- universality, Kreweras ----------
def cyclic_interval(m):
    for s in range(n):
        for length in range(1, n + 1):
            if sum(1 << ((s + t) % n) for t in range(length)) == m:
                return True
    return False

universal = [len(p) == 1 and cyclic_interval(p[0]) for p in NC]

def kreweras(p):
    # in-between point k' sits between k and k+1; label it k
    lab = [-1] * n
    for b in p:
        mn = min(elems(b))
        for e in elems(b):
            lab[e] = mn
    lab = [i if lab[i] < 0 else lab[i] for i in range(n)]
    blocks = []
    parent = list(range(n))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for k in range(n):
        for l in range(k + 1, n):
            arc = set(range(k + 1, l + 1))
            ok = all(lab[i] != lab[j] for i in arc for j in range(n) if j not in arc)
            if ok:
                parent[find(k)] = find(l)
    comp = {}
    for k in range(n):
        comp.setdefault(find(k), 0)
        comp[find(k)] |= 1 << k
    return canon(list(comp.values()))

K = [idx[kreweras(p)] for p in NC]

# ---------- pairs and compat masks ----------
pairs = [(p, c) for p in range(n) for c in range(1, n - 1)]
NP = len(pairs)
adj_bits = sum(1 << t for t, (p, c) in enumerate(pairs) if c in (1, n - 2))

def arcs(p, c):
    a1 = sum(1 << ((p + t) % n) for t in range(1, c + 1))
    a2 = sum(1 << ((p + t) % n) for t in range(c + 1, n))
    return a1, a2

ARCS = [arcs(p, c) for (p, c) in pairs]

def compat_mask(part):
    m = 0
    for t, (p, c) in enumerate(pairs):
        a1, a2 = ARCS[t]
        if all((b >> p & 1) or (b & a1 == b) or (b & a2 == b) for b in part):
            m |= 1 << t
    return m

CM = [compat_mask(p) for p in NC]

# ---------- chambers: maximal chains of the proper part ----------
children = [[j for j in range(N) if leq[i, j] and rank[j] == rank[i] + 1] for i in range(N)]
cham_masks = {}
def dfs_ch(i, mask, chain):
    if rank[i] == n - 2:
        if mask not in cham_masks:
            cham_masks[mask] = tuple(chain)
        return
    for j in children[i]:
        dfs_ch(j, mask & CM[j], chain + [j])
for i in range(N):
    if rank[i] == 1:
        dfs_ch(i, CM[i], [i])

def minimal_masks(masks):
    ms = sorted(set(masks), key=popc)
    out = []
    for m in ms:
        if not any(o & m == o for o in out):
            out.append(m)
    return out

min_all = minimal_masks(cham_masks.keys())
min_adj = minimal_masks(m & adj_bits for m in cham_masks.keys())

cache_all, cache_adj = {}, {}
def IV_all(mF):
    if mF not in cache_all:
        cache_all[mF] = any(o & mF == 0 for o in min_all)
    return cache_all[mF]
def IV_adj(mF):
    a = mF & adj_bits
    if a not in cache_adj:
        cache_adj[a] = any(o & a == 0 for o in min_adj)
    return cache_adj[a]

def cond_I(ranks):
    miss = set(range(1, n - 1)) - set(ranks)
    return any(r in miss and r + 1 in miss for r in miss)

def cond_III(chain):
    seq = [ZERO] + list(chain) + [ONE]
    return any(G[seq[t], seq[t + 1]] for t in range(len(seq) - 1))

def chain_mask(chain):
    m = (1 << NP) - 1
    for i in chain:
        m &= CM[i]
    return m

# ---------- sanity checks ----------
assert all(rank[K[i]] == n - 1 - rank[i] for i in range(N)), "Kreweras rank"
assert len(set(K)) == N, "Kreweras bijective"
for i in range(N):
    for j in range(N):
        if leq[i, j]:
            assert leq[K[j], K[i]], "Kreweras order-reversing"
assert all(universal[K[i]] == universal[i] for i in range(N) if i not in (ZERO, ONE))

def show(i):
    p = NC[i]
    return "{" + ",".join("".join(str(e + 1) if n < 10 else str(e + 1) + "." for e in elems(b)) for b in p) + "}"

# ---------- main search ----------
up = [[j for j in range(N) if leq[i, j] and rank[j] > rank[i] and j != ONE] for i in range(N)]
stats = dict(I=0, I_II=0, I_II_III=0, IV_adj=0, IV_all=0, dual_mismatch=0)
surv_all = []
surv_adj_examples = []
check_dual = n <= 8

def dual_chain(chain):
    return sorted((K[c] for c in chain), key=lambda t: rank[t])

def conds(chain):
    ranks = [rank[c] for c in chain]
    I = cond_I(ranks)
    II = any(not universal[c] for c in chain)
    III = cond_III(chain)
    m = chain_mask(chain)
    return I, II, III, IV_adj(m), IV_all(m)

def dfs(chain, mask):
    ranks = [rank[c] for c in chain]
    if not cond_I(ranks):
        return  # adding vertices only removes missing ranks
    stats["I"] += 1
    if any(not universal[c] for c in chain):
        stats["I_II"] += 1
        III = cond_III(chain)
        a = IV_adj(mask) if III else False
        b = IV_all(mask) if III else False
        if check_dual:
            d = conds(dual_chain(chain))
            if d != (True, True, III, IV_adj(mask) if III else d[3], IV_all(mask) if III else d[4]):
                stats["dual_mismatch"] += 1
        if III:
            stats["I_II_III"] += 1
            if a:
                stats["IV_adj"] += 1
                if len(surv_adj_examples) < 3:
                    surv_adj_examples.append(list(chain))
            if b:
                stats["IV_all"] += 1
                surv_all.append(list(chain))
    for j in up[chain[-1]]:
        dfs(chain + [j], mask & CM[j])

for i in range(N):
    if i not in (ZERO, ONE):
        dfs([i], CM[i])

print("n =", n, "| #NCP_n =", N, "| failing pairs =", nfail, "| pairs =", NP)
print("distinct chamber masks:", len(cham_masks), "| minimal (all pairs):", len(min_all), "| minimal (adjacent pairs):", len(min_adj))
print("stats:", stats)
for ch in surv_adj_examples:
    print("IV_adj survivor example:", " < ".join(show(c) for c in ch))
print("IV_all survivors:", len(surv_all))
for ch in surv_all[:int(sys.argv[2]) if len(sys.argv) > 2 else 5]:
    m = chain_mask(ch)
    wit = next(o for o in min_all if o & m == 0)
    C = cham_masks[wit]
    print("  F =", " < ".join(show(c) for c in ch), "| F* =", " < ".join(show(c) for c in dual_chain(ch)),
          "| witness C =", " < ".join(show(c) for c in C))
