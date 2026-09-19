"""Cayley ball of Gamma_3 = <a,b,c | x^3, Heisenberg relations on each pair> inside a finite
3-quotient Q, and a certificate that the ball of radius R maps injectively into Q.

Q is read from an export of export_tower.g (right action of a,b,c on A\\Q with A-cocycle):
an element is alpha*T[i] with alpha in the abelian group A; (alpha T[i]) x = (alpha+al(i,x)) T[j].

Certificate.  K = Cayley 2-complex of the Q-ball of radius Rb, with every 2-cell of Gamma's
presentation x^3, (xy)^3, (xy^2)^3 ({x,y} = {a,b},{b,c},{c,a}) whose boundary lies in K.
BFS-tree edges are 'dead'.  A cell whose edges are all dead except one edge occurring once
kills that edge.  A dead edge (g,gx) satisfies L(g)x = L(gx) in Gamma, where L is the lift along
the BFS tree (its fundamental loop is null-homotopic in K, and K sits in Cay(Gamma)/P).
If every edge with both ends at distance <= R is dead, L is a bijection from the Q-ball of
radius R onto the Gamma-ball of radius R that preserves all Cayley edges (see the proof note).
"""
import sys, numpy as np

def load_q(path):
    ords, m, act = None, None, {}
    for line in open(path):
        if line.startswith('ORDS'): ords = eval(line[5:])
        elif line.startswith('M '): m = int(line[2:])
        elif line.startswith('R '):
            t = line.split(None, 4); x, i, j = int(t[1]) - 1, int(t[2]), int(t[3])
            act[(x, i)] = (j, eval(t[4]))
    r = len(ords)
    sig = np.zeros((3, m), dtype=np.int64); al = np.zeros((3, m, r), dtype=np.int16)
    for (x, i), (j, a) in act.items():
        sig[x, i] = j; al[x, i] = a
    return np.array(ords, dtype=np.int16), m, sig, al

class Q:
    def __init__(self, path):
        self.ords, self.m, self.sig, self.al = load_q(path)
        self.r = len(self.ords)
        w = np.ones(self.r, dtype=np.int64)
        for k in range(1, self.r): w[k] = w[k - 1] * int(self.ords[k - 1])
        self.w = w; self.nA = int(w[-1] * int(self.ords[-1]))
        assert self.nA * self.m < 2 ** 62
    def mul(self, I, Al, x):  # right multiplication of a batch by generator x (0,1,2 = a,b,c)
        return self.sig[x, I], (Al + self.al[x, I]) % self.ords
    def key(self, I, Al):
        return I.astype(np.int64) * self.nA + (Al.astype(np.int64) @ self.w)

def ball(q, R):
    """Layered BFS.  Returns keys (sorted), dist, and nbr[x] = index of g*x (or -1 outside)."""
    I = np.zeros(1, dtype=np.int64); Al = np.zeros((1, q.r), dtype=np.int16)
    layers = [(I, Al)]; seen = q.key(I, Al)
    for d in range(1, R + 1):
        I0, A0 = layers[-1]; cand_I, cand_A = [], []
        for x in range(3):
            I1, A1 = q.mul(I0, A0, x); cand_I.append(I1); cand_A.append(A1)
            I2, A2 = q.mul(I1, A1, x); cand_I.append(I2); cand_A.append(A2)
        CI = np.concatenate(cand_I); CA = np.concatenate(cand_A)
        k = q.key(CI, CA); k, pos = np.unique(k, return_index=True)
        new = ~np.isin(k, seen)
        layers.append((CI[pos[new]], CA[pos[new]])); seen = np.concatenate([seen, k[new]])
        print(f"  radius {d}: sphere {new.sum()}, ball {len(seen)}", flush=True)
    I = np.concatenate([l[0] for l in layers]); Al = np.concatenate([l[1] for l in layers])
    dist = np.concatenate([np.full(len(l[0]), d, dtype=np.int8) for d, l in enumerate(layers)])
    keys = q.key(I, Al); order = np.argsort(keys)
    keys, I, Al, dist = keys[order], I[order], Al[order], dist[order]
    nbr = np.empty((3, len(keys)), dtype=np.int64)
    for x in range(3):
        I1, A1 = q.mul(I, Al, x); k1 = q.key(I1, A1)
        p = np.searchsorted(keys, k1); p[p >= len(keys)] = 0
        nbr[x] = np.where(keys[p] == k1, p, -1)
    return keys, dist, nbr

PAIRS = [(0, 1), (1, 2), (2, 0)]
def cells(nbr):
    """All relator cells (as arrays of edge ids g*3+x) whose boundary lies in the ball."""
    N = nbr.shape[1]; out = []
    words = [[x] * 3 for x in range(3)]
    for x, y in PAIRS: words += [[x, y] * 3, [x, y, y] * 3]
    for wd in words:
        g = np.arange(N); ok = np.ones(N, bool); eds = []
        for s in wd:
            eds.append(g * 3 + s); h = nbr[s][np.where(ok, g, 0)]; ok &= h >= 0; g = np.where(ok, h, 0)
        assert np.all(g[ok] == np.arange(N)[ok]), "relator does not close in Q"
        out.append(np.stack(eds, 1)[ok].astype(np.int32))
    return out

def tree_edges(nbr, dist):
    N = nbr.shape[1]; par = np.full(N, -1, dtype=np.int64)
    for x in range(3):
        h = nbr[x][np.maximum(nbr[x], 0)]; h2 = np.where(nbr[x] >= 0, h, -1)  # h2 = g*x^2
        # edge (g,x): g -> g x
        c1 = (nbr[x] >= 0) & (dist[np.maximum(nbr[x], 0)] == dist - 1) & (par < 0)
        par[c1] = np.arange(N)[c1] * 3 + x
        c2 = (h2 >= 0) & (dist[np.maximum(h2, 0)] == dist - 1) & (par < 0)
        par[c2] = h2[c2] * 3 + x
    assert np.all(par[dist > 0] >= 0)
    return par[dist > 0]

def certify(nbr, dist, R):
    N = nbr.shape[1]
    exists = (nbr >= 0).T.reshape(-1)          # edge g*3+x exists iff g*x in ball
    alive = exists.copy(); alive[tree_edges(nbr, dist)] = False
    C = cells(nbr); it = 0
    while True:
        ch = 0
        for c in C:
            na = alive[c].sum(1); sel = na == 1
            if not sel.any(): continue
            e = c[sel][np.arange(sel.sum()), alive[c[sel]].argmax(1)]
            e = e[alive[e]]; alive[e] = False; ch += len(np.unique(e))
        it += 1
        if ch == 0: break
    g = np.arange(N * 3) // 3
    x = np.arange(N * 3) % 3
    inner = exists & (dist[g] <= R) & (dist[np.maximum(nbr.T.reshape(-1), 0)] <= R)
    bad = int((alive & inner).sum())
    print(f"  certify: {it} sweeps, alive edges {int(alive.sum())} of {int(exists.sum())}; alive inside radius {R}: {bad}")
    return bad == 0
