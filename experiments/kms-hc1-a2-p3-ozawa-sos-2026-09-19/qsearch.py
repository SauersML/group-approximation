"""Commuting-graph search in Gamma_3: candidates from a finite quotient Q, every edge proven exactly.

Nodes are infinite-order elements (words).  For a node k, candidates are the x in the Q-ball of
radius r with x k = k x in Q; each accepted edge [k, x] = 1 is proven in Gamma_3 by tube.certify_word,
and |x| = oo is proven by x^3 != 1 in Q (torsion of Gamma_3 has exponent 3).
Goal: an infinite-order element commuting with b (and with c) in the component of t_a."""
import sys, time, numpy as np
from qball import Q, ball
from tube import certify_word, W, inv_word, commutator, LET

def wstr(w): return ''.join(LET[s] for s in w)

class QBall:
    def __init__(self, q, r):
        self.q = q; self.keys, self.dist, self.nbr = ball(q, r); N = len(self.keys)
        self.I = self.keys // q.nA; code = self.keys % q.nA
        self.A = np.stack([(code // q.w[j]) % q.ords[j] for j in range(q.r)], 1).astype(np.int16)
        self.par = np.full(N, -1, dtype=np.int64); self.last = np.full(N, -1, dtype=np.int64)
        for x in range(3):
            ok = self.nbr[x] >= 0; g = np.nonzero(ok)[0]; h = self.nbr[x][ok]
            c1 = (self.dist[h] == self.dist[g] + 1) & (self.par[h] < 0)      # h = g x
            self.par[h[c1]] = g[c1]; self.last[h[c1]] = x
            c2 = (self.dist[g] == self.dist[h] + 1) & (self.par[g] < 0)      # g = h x^-1
            self.par[g[c2]] = h[c2]; self.last[g[c2]] = x + 3
        self.order = np.argsort(self.dist, kind='stable')
        self.root = int(np.searchsorted(self.keys, 0))
    def word(self, g):
        w = []
        while g != self.root: w.append(int(self.last[g])); g = int(self.par[g])
        return w[::-1]
    def apply(self, I, A, s):
        x = s % 3
        for _ in range(1 if s < 3 else 2): I, A = self.q.mul(I, A, x)
        return I, A
    def apply_word(self, I, A, w):
        for s in w: I, A = self.apply(I, A, s)
        return I, A
    def elem(self, w):
        return self.apply_word(np.zeros(1, dtype=np.int64), np.zeros((1, self.q.r), dtype=np.int16), w)
    def centraliser(self, w):
        """indices x of the ball with x*w = w*x in Q."""
        q = self.q; N = len(self.keys)
        RI, RA = self.apply_word(self.I, self.A, w); Rk = q.key(RI, RA)
        kI, kA = self.elem(w); LI = np.zeros(N, dtype=np.int64); LA = np.zeros((N, q.r), dtype=np.int16)
        LI[self.root] = kI[0]; LA[self.root] = kA[0]
        for d in range(1, int(self.dist.max()) + 1):
            lay = np.nonzero(self.dist == d)[0]
            for s in range(6):
                g = lay[self.last[lay] == s]
                if len(g) == 0: continue
                I1, A1 = self.apply(LI[self.par[g]], LA[self.par[g]], s); LI[g] = I1; LA[g] = A1
        return np.nonzero(q.key(LI, LA) == Rk)[0]
    def infinite(self, w):
        I, A = self.elem(w * 3); return int(self.q.key(I, A)[0]) != 0

def prove(q, w, rhos=(2, 3, 4, 5)):
    for rho in rhos:
        ok, info = certify_word(q, w, rho)
        if ok: return rho
    return None

def search(qfile, r, start, maxnodes, targets=('a', 'b', 'c')):
    t0 = time.time(); q = Q(qfile); QB = QBall(q, r)
    print(f"Q-ball radius {r}: {len(QB.keys)} elements [{time.time()-t0:.0f}s]", flush=True)
    key = lambda w: int(q.key(*QB.elem(w))[0])
    tg = {nm: key(W(nm)) for nm in targets}
    nodes = {key(start): (start, None, None)}; queue = [key(start)]; found = {}; head = 0; nfail = 0
    while head < len(queue) and len(nodes) < maxnodes and len(found) < len(tg):
        kk = queue[head]; head += 1; wk = nodes[kk][0]
        cands = QB.centraliser(wk)
        ckeys = set(QB.keys[cands].tolist())
        for nm, tk in tg.items():
            if nm not in found and tk in ckeys:
                rho = prove(q, commutator(wk, W(nm)))
                if rho: found[nm] = (kk, rho); print(f"  FOUND {nm} commutes with {wstr(wk)} (tube rho={rho})", flush=True)
        for x in cands.tolist():
            xk = int(QB.keys[x])
            if xk in nodes or x == QB.root: continue
            wx = QB.word(x)
            if not QB.infinite(wx): continue
            rho = prove(q, commutator(wk, wx))
            if rho is None: nfail += 1; continue
            nodes[xk] = (wx, kk, rho); queue.append(xk)
        if head % 50 == 0:
            print(f"  processed {head}, nodes {len(nodes)}, unproven {nfail} [{time.time()-t0:.0f}s]", flush=True)
    return q, nodes, found

def chain(nodes, k):
    out = []
    while k is not None: out.append(nodes[k]); k = nodes[k][1]
    return out[::-1]

if __name__ == '__main__':
    qfile, r, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    start = W(sys.argv[4]) if len(sys.argv) > 4 else W('bABcaC')
    q, nodes, found = search(qfile, r, start, maxn)
    print(f"component nodes explored: {len(nodes)}; found: {sorted(found)}")
    for nm, (k, rho) in found.items():
        print(f"chain to {nm}:", ' ~ '.join(wstr(w) for w, _, _ in chain(nodes, k)), f"~ {nm}")
