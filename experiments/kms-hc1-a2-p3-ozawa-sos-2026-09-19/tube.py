"""Exact certificate that a word w is trivial in Gamma_3, from a finite 3-quotient Q.

Let Y be the Cayley 2-complex of Q with one 2-cell for each relator of Gamma_3's presentation
(x^3, (xy)^3, (xy^2)^3 for {x,y} = {a,b},{b,c},{c,a}; these are equivalent to the Heisenberg
relators given x^3 = y^3 = 1).  The Cayley 2-complex of Gamma_3 is simply connected and covers Y,
so a closed edge path in Y that is null-homotopic in Y lifts to a closed path in Cay(Gamma_3),
i.e. its label is trivial in Gamma_3.

Certificate: K = subcomplex of Y spanned by the tube (all Q-elements within distance rho of the
path of w), with every relator cell whose boundary lies in the tube.  Edges of a BFS spanning tree
of K are 'dead'; a cell with exactly one alive edge-occurrence kills that edge (the edge is then
homotopic rel endpoints, inside K, to a path of dead edges).  If every edge on the path of w is
dead, the path is homotopic in K to a tree loop, hence null-homotopic, so w = 1 in Gamma_3.
Soundness does not depend on Q being large; a larger Q only makes the tube more likely to work."""
import numpy as np
from qball import Q, cells

def path_elems(q, w):
    I = np.zeros(1, dtype=np.int64); A = np.zeros((1, q.r), dtype=np.int16); PI, PA = [I], [A]
    for s in w:
        x = s % 3
        for _ in range(1 if s < 3 else 2): I, A = q.mul(I, A, x)
        PI.append(I); PA.append(A)
    return np.concatenate(PI), np.concatenate(PA)

def tube_complex(q, w, rho):
    PI, PA = path_elems(q, w)
    if q.key(PI[-1:], PA[-1:])[0] != 0: return None          # not even closed in Q
    I, A = PI, PA; keys = np.unique(q.key(I, A)); layerI, layerA = I, A
    for _ in range(rho):
        cI, cA = [], []
        for x in range(3):
            I1, A1 = q.mul(layerI, layerA, x); I2, A2 = q.mul(I1, A1, x)
            cI += [I1, I2]; cA += [A1, A2]
        CI = np.concatenate(cI); CA = np.concatenate(cA); k = q.key(CI, CA)
        k, pos = np.unique(k, return_index=True); new = ~np.isin(k, keys)
        layerI, layerA = CI[pos[new]], CA[pos[new]]; keys = np.union1d(keys, k[new])
    # recover (I, A) for all keys
    allI = keys // q.nA; code = keys % q.nA
    allA = np.stack([(code // q.w[j]) % q.ords[j] for j in range(q.r)], 1).astype(np.int16)
    N = len(keys); nbr = np.empty((3, N), dtype=np.int64)
    for x in range(3):
        I1, A1 = q.mul(allI, allA, x); k1 = q.key(I1, A1)
        p = np.searchsorted(keys, k1); p[p >= N] = 0; nbr[x] = np.where(keys[p] == k1, p, -1)
    return keys, nbr, q.key(PI, PA)

def bfs_dist(nbr, root):
    N = nbr.shape[1]; dist = np.full(N, -1, dtype=np.int64); dist[root] = 0; fr = np.array([root]); d = 0
    inv = np.full((3, N), -1, dtype=np.int64)
    for x in range(3):
        ok = nbr[x] >= 0; inv[x][nbr[x][ok]] = np.nonzero(ok)[0]
    while len(fr):
        d += 1; cand = np.concatenate([nbr[:, fr].ravel(), inv[:, fr].ravel()])
        cand = np.unique(cand[cand >= 0]); cand = cand[dist[cand] < 0]; dist[cand] = d; fr = cand
    return dist

def tree_edges(nbr, dist):
    """one parent edge per vertex at dist > 0 (edge id g*3+x means g -> g x); handles both orientations."""
    N = nbr.shape[1]; par = np.full(N, -1, dtype=np.int64)
    for x in range(3):
        ok = nbr[x] >= 0; g = np.nonzero(ok)[0]; h = nbr[x][ok]
        c1 = (dist[h] == dist[g] - 1) & (par[g] < 0); par[g[c1]] = g[c1] * 3 + x      # g's parent is g x
        c2 = (dist[g] == dist[h] - 1) & (par[h] < 0); par[h[c2]] = g[c2] * 3 + x      # h's parent is g = h x^-1
    assert np.all(par[dist > 0] >= 0)
    return par[dist > 0]

def certify_word(q, w, rho, verbose=False):
    tc = tube_complex(q, w, rho)
    if tc is None: return False, 'not closed in Q'
    keys, nbr, pkeys = tc; N = len(keys)
    root = int(np.searchsorted(keys, 0)); dist = bfs_dist(nbr, root)
    assert np.all(dist >= 0), "tube not connected"
    exists = (nbr >= 0).T.reshape(-1); alive = exists.copy(); alive[tree_edges(nbr, dist)] = False
    C = cells(nbr)
    while True:
        ch = 0
        for c in C:
            sel = alive[c].sum(1) == 1
            if not sel.any(): continue
            e = c[sel][np.arange(sel.sum()), alive[c[sel]].argmax(1)]; e = np.unique(e[alive[e]])
            alive[e] = False; ch += len(e)
        if ch == 0: break
    pidx = np.searchsorted(keys, pkeys); bad = 0
    for t, s in enumerate(w):
        g, h = int(pidx[t]), int(pidx[t + 1])
        x = s % 3
        eid = g * 3 + x if s < 3 else h * 3 + x          # edge (g, g x) or (g x^-1, g)
        assert (s < 3 and nbr[x][g] == h) or (s >= 3 and nbr[x][h] == g)
        bad += bool(alive[eid])
    if verbose: print(f"    tube rho={rho}: {N} vertices, alive {int(alive.sum())}/{int(exists.sum())}, alive on path {bad}")
    return bad == 0, f"tube {N}, alive on path {bad}"

LET = 'abcABC'
def W(s): return [LET.index(ch) for ch in s]
def inv_word(w): return [(s + 3) % 6 for s in reversed(w)]
def commutator(u, v): return inv_word(u) + inv_word(v) + u + v
