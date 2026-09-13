#!/usr/bin/env python3
# Meet-in-the-middle search for Burau kernel elements in K_4 = <A14, A24, A34>, the point-pushing subgroup
# of strand 4 in B_4 (free of rank 3).  Every reduced word u of length <= L in the six letters is enumerated;
# its Burau matrix is evaluated at t = T0 modulo the prime P and hashed.  If u != v are reduced words with
# rho(u) = rho(v) exactly, their evaluations and hashes agree, so they appear as a collision.  Every
# collision is re-checked exactly over Z[t, 1/t].  Hence "no exact collision" means: no nontrivial element
# of K_4 of free length <= 2L lies in ker rho_4 (each such element factors as u v^{-1}, |u|, |v| <= L, u != v).
# Levels <= H are built whole; deeper levels are built in chunks of CH level-H words to bound memory.
# Usage: python3 burau_k4_search.py <k4|control> <L> <H> <CH>
#   control: the six letters are sigma1..3 and inverses as FREE letters, so braid relations must collide.
import sys, time
import numpy as np

MODE, L, H, CH = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
N = 4
P, T0 = 1000000007, 123456789  # P < 2^30: a sum of four products stays below 2^62

def sigma_mod(i, inv):
    M = np.eye(N, dtype=np.int64)
    if not inv:
        M[i-1, i-1] = (1 - T0) % P; M[i-1, i] = T0 % P; M[i, i-1] = 1; M[i, i] = 0
    else:
        ti = pow(T0, P - 2, P)
        M[i-1, i-1] = 0; M[i-1, i] = 1; M[i, i-1] = ti; M[i, i] = (1 - ti) % P
    return M

def word_mod(letters):
    M = np.eye(N, dtype=np.int64)
    for s in letters:
        M = (M @ sigma_mod(abs(s), s < 0)) % P
    return M

def artin_gen(j):  # A_{j4} = (s3 ... s_{j+1}) s_j^2 (s_{j+1}^{-1} ... s3^{-1})
    pre = list(range(3, j, -1))
    return pre + [j, j] + [-x for x in reversed(pre)]

BASE = [artin_gen(1), artin_gen(2), artin_gen(3)] if MODE == "k4" else [[1], [2], [3]]
LETTERS = BASE + [[-x for x in reversed(g)] for g in BASE]  # letter k+3 is the inverse of letter k
INV = np.array([3, 4, 5, 0, 1, 2], dtype=np.int8)
G = [word_mod(LETTERS[k]) for k in range(6)]
R = np.random.default_rng(20260913).integers(1, 2**63, size=N * N, dtype=np.uint64)

def hsh(m):
    return (m.reshape(m.shape[0], N * N).astype(np.uint64) * R).sum(axis=1, dtype=np.uint64)

def extend(mats, last):
    om, op, ol = [], [], []
    for k in range(6):
        idx = np.nonzero(last != INV[k])[0]
        if idx.size == 0:
            continue
        om.append((mats[idx] @ G[k]) % P); op.append(idx); ol.append(np.full(idx.size, k, dtype=np.int8))
    return np.concatenate(om), np.concatenate(op), np.concatenate(ol)

t0 = time.time()
HS = [[] for _ in range(L + 1)]; PA = [[] for _ in range(L + 1)]; LE = [[] for _ in range(L + 1)]
CNT = [0] * (L + 1)
mats = np.eye(N, dtype=np.int64)[None]; last = np.array([-1], dtype=np.int8)
HS[0].append(hsh(mats)); PA[0].append(np.zeros(1, dtype=np.uint32)); LE[0].append(last); CNT[0] = 1
for lev in range(1, min(H, L) + 1):
    mats, par, last = extend(mats, last)
    HS[lev].append(hsh(mats)); PA[lev].append(par.astype(np.uint32)); LE[lev].append(last)
    CNT[lev] = mats.shape[0]
    print(f"level {lev}: {CNT[lev]} words, {time.time() - t0:.1f}s", flush=True)
if L > H:
    for s in range(0, mats.shape[0], CH):
        cm, cl, off = mats[s:s + CH], last[s:s + CH], s
        for lev in range(H + 1, L + 1):
            cm, par, cl = extend(cm, cl)
            HS[lev].append(hsh(cm)); PA[lev].append((par + off).astype(np.uint32)); LE[lev].append(cl)
            off = CNT[lev]; CNT[lev] += cm.shape[0]
    for lev in range(H + 1, L + 1):
        print(f"level {lev}: {CNT[lev]} words", flush=True)
    print(f"generation done, {time.time() - t0:.1f}s", flush=True)
del mats
hashes = [np.concatenate(x) for x in HS]; del HS
parents = [np.concatenate(x) for x in PA]; del PA
lets = [np.concatenate(x) for x in LE]; del LE
offs = np.cumsum([0] + [h.size for h in hashes])
allh = np.concatenate(hashes); del hashes
order = np.argsort(allh)
sh = allh[order]
dup = np.nonzero(sh[1:] == sh[:-1])[0]
del sh
print(f"total words {allh.size}, hash collisions {dup.size}, {time.time() - t0:.1f}s", flush=True)

def locate(g):
    lev = int(np.searchsorted(offs, g, side="right") - 1)
    return lev, int(g - offs[lev])

def word_of(lev, idx):
    w = []
    while lev > 0:
        w.append(int(lets[lev][idx])); idx = int(parents[lev][idx]); lev -= 1
    return w[::-1]

def padd(a, b):
    c = dict(a)
    for e, v in b.items():
        c[e] = c.get(e, 0) + v
        if c[e] == 0:
            del c[e]
    return c

def pmul(a, b):
    c = {}
    for e1, v1 in a.items():
        for e2, v2 in b.items():
            c[e1 + e2] = c.get(e1 + e2, 0) + v1 * v2
    return {e: v for e, v in c.items() if v != 0}

def mmul(A, B):
    C = [[{} for _ in range(N)] for _ in range(N)]
    for i in range(N):
        for j in range(N):
            acc = {}
            for k in range(N):
                acc = padd(acc, pmul(A[i][k], B[k][j]))
            C[i][j] = acc
    return C

def esig(i, inv):
    M = [[({0: 1} if r == c else {}) for c in range(N)] for r in range(N)]
    if not inv:
        M[i-1][i-1] = {0: 1, 1: -1}; M[i-1][i] = {1: 1}; M[i][i-1] = {0: 1}; M[i][i] = {}
    else:
        M[i-1][i-1] = {}; M[i-1][i] = {0: 1}; M[i][i-1] = {-1: 1}; M[i][i] = {0: 1, -1: -1}
    return M

def is_id(M):
    return all(M[r][c] == ({0: 1} if r == c else {}) for r in range(N) for c in range(N))

MAXCHK = 5000
exact = 0; checked = 0
for d in dup[:MAXCHK]:
    g1, g2 = int(order[d]), int(order[d + 1])
    u, v = word_of(*locate(g1)), word_of(*locate(g2))
    red = []
    for k in u + [int(INV[k]) for k in reversed(v)]:
        if red and red[-1] == INV[k]:
            red.pop()
        else:
            red.append(k)
    M = [[({0: 1} if r == c else {}) for c in range(N)] for r in range(N)]
    for s in [x for k in red for x in LETTERS[k]]:
        M = mmul(M, esig(abs(s), s < 0))
    ok = is_id(M); exact += ok; checked += 1
    if checked <= 10:
        print(f"collision reduced={red} exact_kernel={ok}", flush=True)
print(f"RESULT mode={MODE} L={L} max_free_length={2 * L} words={allh.size} hash_collisions={dup.size} "
      f"checked={checked} exact_kernel={exact} time={time.time() - t0:.1f}s", flush=True)
