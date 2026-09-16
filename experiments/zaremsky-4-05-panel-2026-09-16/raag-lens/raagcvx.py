"""Independent RAAG Cayley graph code: reduced words, convex hulls (closure under 2-intervals),
distance matrices. Letters: 2g (g) and 2g+1 (g^-1)."""
import itertools
from collections import deque
import numpy as np

class RAAG:
    def __init__(self, n, edges):
        self.n = n
        self.C = [[g == h for h in range(n)] for g in range(n)]
        for a, b in edges:
            self.C[a][b] = self.C[b][a] = True
    def nf(self, w):
        w = list(w); out = []
        while w:
            cand = [i for i in range(len(w)) if all(self.C[w[i] >> 1][w[j] >> 1] for j in range(i))]
            i = min(cand, key=lambda i: w[i]); out.append(w.pop(i))
        return tuple(out)
    def mul(self, w, l):
        g = l >> 1; w = list(w)
        for i in range(len(w) - 1, -1, -1):
            h = w[i] >> 1
            if h == g:
                if w[i] == l ^ 1:
                    del w[i]; return self.nf(w)
                break
            if not self.C[g][h]:
                break
        w.append(l); return self.nf(w)
    def nbrs(self, w):
        return [self.mul(w, l) for l in range(2 * self.n)]
    def inv(self, w):
        return self.nf([l ^ 1 for l in reversed(w)])
    def dist(self, a, b):
        x = self.inv(a)
        for l in b:
            x = self.mul(x, l)
        return len(x)

def ball(G, R):
    seen = {(): 0}; q = deque([()])
    while q:
        u = q.popleft()
        if seen[u] == R: continue
        for v in G.nbrs(u):
            if v not in seen:
                seen[v] = seen[u] + 1; q.append(v)
    return set(seen)

def hull(G, S):
    K = set(S)
    changed = True
    while changed:
        changed = False
        for u in list(K):
            # common neighbours of u and w=u*x*y with w in K
            N1 = G.nbrs(u)
            for v in N1:
                for w in G.nbrs(v):
                    if w in K and w != u and G.dist(u, w) == 2:
                        # all common neighbours of u, w
                        for z in N1:
                            if z not in K and G.dist(z, w) == 1:
                                K.add(z); changed = True
    return K

def dmat(G, K):
    K = sorted(K, key=lambda w: (len(w), w)); idx = {w: i for i, w in enumerate(K)}
    n = len(K); D = np.full((n, n), -1.0)
    adj = [[idx[v] for v in G.nbrs(w) if v in idx] for w in K]
    for s in range(n):
        D[s, s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if D[s, v] < 0:
                    D[s, v] = D[s, u] + 1; q.append(v)
    assert (D >= 0).all(), "hull not connected"
    return K, D

def check_isometric(G, K, D, samples=400, seed=1):
    import random
    rnd = random.Random(seed); n = len(K); bad = 0
    for _ in range(samples):
        i, j = rnd.randrange(n), rnd.randrange(n)
        if G.dist(K[i], K[j]) != D[i, j]: bad += 1
    return bad
