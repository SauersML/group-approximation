"""Referee's independent check (2026-09-16) of Lemmas C, J, H of
research/artifacts/zp-cube-complex-jensen-helly-2026-09-16.md.

Independent of raagcube.py.  Median graphs are generated as Roller duals of random
split systems of m points: vertices are orientations (one halfspace per split)
whose chosen halfspaces pairwise intersect as subsets of the points.  We verify by
BFS that the graph is median and that d = Hamming distance, compute coordinate
cubes and cube dimension k, then:
  (J) min Phi over D = {c in box : L_x(c) <= L_x(w)} has no charged empty quadrant;
  (H) min over |X| of max_i (L_{z_i} - rho_i) equals the max over (k+1)-subfamilies,
      with radii hill-climbed to maximise the gap (and the k-subfamily gap reported).
Usage: python3 ref_check.py seed trials
"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
from collections import deque

def gen(rng, m, n):
    pts = list(range(m))
    splits = set()
    tries = 0
    while len(splits) < n and tries < 1000:
        tries += 1
        A = frozenset(p for p in pts if rng.random() < 0.5)
        if 0 < len(A) < m:
            key = min(A, frozenset(pts) - A, key=lambda s: sorted(s))
            splits.add(key)
    splits = list(splits)
    halves = [(frozenset(pts) - S, S) for S in splits]  # halves[h][bit]
    V = []
    for sig in itertools.product((0, 1), repeat=len(splits)):
        ch = [halves[h][sig[h]] for h in range(len(splits))]
        if all(ch[i] & ch[j] for i in range(len(ch)) for j in range(i)):
            V.append(sig)
    return splits, V

def bfs(V):
    idx = {v: i for i, v in enumerate(V)}
    adj = [[] for _ in V]
    for i, v in enumerate(V):
        for h in range(len(v)):
            u = list(v); u[h] ^= 1; u = tuple(u)
            if u in idx: adj[i].append(idx[u])
    D = np.full((len(V), len(V)), -1, dtype=int)
    for s in range(len(V)):
        D[s, s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if D[s, y] < 0: D[s, y] = D[s, x] + 1; q.append(y)
    return D

def check_median(V, D):
    N = len(V)
    I = (D[:, :, None] + D[None, :, :] == D[:, None, :])  # I[a,x,b]: x in I(a,b)
    for a in range(N):
        for b in range(a, N):
            cnt = (I[a, :, b][None, :] & I[b, :, :].T & I[a, :, :].T).sum(axis=1)
            if (cnt != 1).any(): return False
    return True

def cubes(V):
    Vs = set(V); n = len(V[0]); out = []
    for v in V:
        for r in range(n + 1):
            for F in itertools.combinations(range(n), r):
                ok = True
                for sig in itertools.product((0,1), repeat=r):
                    u = list(v)
                    for h, b in zip(F, sig): u[h] = b
                    if tuple(u) not in Vs: ok = False; break
                if ok: out.append((v, F))
    k = max(len(F) for _, F in out)
    # keep maximal
    mx = [(v, F) for v, F in out if len(F) == 0 or True]
    return out, k

def Lrow(x):
    a = np.array([-1.0 if b else 1.0 for b in x]); return a, float(sum(x))

def s_over_cube(rows, v, F, n):
    free = list(F)
    Aub, bub = [], []
    for a, const, rho in rows:
        cst = const - rho + sum(a[h] * v[h] for h in range(n) if h not in F)
        Aub.append([a[h] for h in free] + [-1.0]); bub.append(-cst)
    c = np.zeros(len(free) + 1); c[-1] = 1
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub), bounds=[(0,1)]*len(free)+[(None,None)], method="highs")
    return res.fun

def sX(rows, cub, n):
    return min(s_over_cube(rows, v, F, n) for v, F in cub)

def main():
    seed, trials = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    stats = dict(graphs=0, nonmedian=0, charged=0, helly_fail=0, worst_gap_k1=0.0, teeth_k=0)
    for t in range(trials):
        m = rng.randint(4, 6); n = rng.randint(3, 6)
        splits, V = gen(rng, m, n)
        n = len(splits)
        if len(V) < 3 or n < 2: continue
        D = bfs(V)
        if (D < 0).any() or any(D[i,j] != sum(a != b for a, b in zip(V[i], V[j])) for i in range(len(V)) for j in range(len(V))) or not check_median(V, D):
            stats['nonmedian'] += 1; continue
        cub, k = cubes(V)
        maxcub = [(v, F) for v, F in cub if not any(set(F) < set(G) and all(v[h]==w[h] for h in range(n) if h not in G) for w, G in cub)]
        stats['graphs'] += 1
        # (J)
        for _ in range(3):
            mu = np.array([rng.random() if rng.random() < 0.5 else 0.0 for _ in V], dtype=float)
            if mu.sum() == 0: mu[0] = 1
            mu /= mu.sum()
            w = np.array([sum(mu[i] * V[i][h] for i in range(len(V))) for h in range(n)])
            A = []; b = []
            for x in V:
                a, const = Lrow(x); A.append(a); b.append(a @ w)
            obj = np.sum(A, axis=0)
            res = linprog(obj, A_ub=np.array(A), b_ub=np.array(b), bounds=[(0,1)]*n, method="highs")
            p = res.x
            # charged empty quadrant?
            halves = [(set(i for i in range(len(V)) if V[i][h] == 0), set(i for i in range(len(V)) if V[i][h] == 1)) for h in range(n)]
            for h in range(n):
                for g in range(n):
                    if g == h: continue
                    for bh in (0,1):
                        for bg in (0,1):
                            if not (halves[h][bh] & halves[g][bg]):
                                qa = p[h] if bh else 1 - p[h]; qb = p[g] if bg else 1 - p[g]
                                if min(qa, qb) > 1e-7: stats['charged'] += 1
        # (H) adversarial radii
        cnum = min(len(V), k + 2 + rng.randint(0, 2))
        Z = rng.sample(range(len(V)), cnum)
        rho = [rng.uniform(0, 3) for _ in Z]
        def gaps(rho):
            rows = [Lrow(V[z]) + (r,) for z, r in zip(Z, rho)]
            full = sX(rows, maxcub, n)
            k1 = max(sX([rows[i] for i in T], maxcub, n) for T in itertools.combinations(range(len(Z)), min(k+1, len(Z))))
            kk = max(sX([rows[i] for i in T], maxcub, n) for T in itertools.combinations(range(len(Z)), min(k, len(Z))))
            return full - k1, full - kk
        g1, gk = gaps(rho)
        for it in range(25):
            r2 = [r + rng.gauss(0, 0.3) for r in rho]
            h1, hk = gaps(r2)
            gk = max(gk, hk)
            if h1 > g1 - 1e-12 or (g1 <= 1e-9 and hk >= gk):
                rho, g1 = r2, max(h1, g1)
        stats['worst_gap_k1'] = max(stats['worst_gap_k1'], g1)
        if g1 > 1e-7: stats['helly_fail'] += 1
        if gk > 1e-7: stats['teeth_k'] += 1
        print('trial', t, 'V', len(V), 'n', n, 'k', k, 'centres', cnum, 'gap_k+1 %.3g gap_k %.3g' % (g1, gk), flush=True)
    print(stats)

main()
