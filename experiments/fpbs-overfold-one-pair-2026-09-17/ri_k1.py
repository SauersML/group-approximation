"""Exact test of relative inertia (RI_B) at k = 1, all g in F at once.

B = L_j = phi^j(F).  For X = phi^j(X_0):
  every J = <X, g> is an arc extension (then rk(Y:X) <= 1 by SHN, see the
  artifact) or a one-pair fold of Gamma_X (Lemma 1).  For each one-pair fold J
  we compute Y = J cap B by pullback and decide rk(Y : X) <= 1 exactly:
    rk(Y:X) <= 1  iff  Y = X, or Gamma_X embeds in Gamma_Y with rk Y = rk X + 1,
                   or Gamma_Y is a one-pair fold of Gamma_X.
Any failure is a counterexample to (RI_{L_j}) at k = 1.
usage: ri_k1.py j seed trials maxgens maxlen
"""
import random, sys
from folding import *


def pullback(n1, E1, n2, E2):
    """Based component of the product of two folded graphs, as a graph."""
    out2 = {}
    for (u, l, v) in E2:
        out2.setdefault((u, l), []).append(v)
    in2 = {}
    for (u, l, v) in E2:
        in2.setdefault((v, l), []).append(u)
    adj1o, adj1i = {}, {}
    for (u, l, v) in E1:
        adj1o.setdefault(u, []).append((l, v))
        adj1i.setdefault(v, []).append((l, u))
    idx = {(0, 0): 0}
    q = [(0, 0)]
    edges = set()
    while q:
        p = q.pop()
        x, y = p
        for (l, x2) in adj1o.get(x, []):
            for y2 in out2.get((y, l), []):
                t = (x2, y2)
                if t not in idx:
                    idx[t] = len(idx)
                    q.append(t)
                edges.add((idx[p], l, idx[t]))
        for (l, x2) in adj1i.get(x, []):
            for y2 in in2.get((y, l), []):
                t = (x2, y2)
                if t not in idx:
                    idx[t] = len(idx)
                    q.append(t)
                edges.add((idx[t], l, idx[p]))
    return len(idx), sorted(edges)


def compact(n, edges):
    alive, E = core_based(n, edges)
    ren = {v: i for i, v in enumerate(sorted(alive))}
    return len(ren), sorted((ren[u], l, ren[v]) for (u, l, v) in E)


def embeds(nx, Ex, ny, Ey):
    """Is the based immersion Gamma_X -> Gamma_Y injective on vertices?"""
    outy = {(u, l): v for (u, l, v) in Ey}
    iny = {(v, l): u for (u, l, v) in Ey}
    m = {0: 0}
    q = [0]
    adj = {}
    for (u, l, v) in Ex:
        adj.setdefault(u, []).append((l, v, 1))
        adj.setdefault(v, []).append((l, u, -1))
    while q:
        v = q.pop()
        for (l, t, d) in adj.get(v, []):
            img = outy.get((m[v], l)) if d == 1 else iny.get((m[v], l))
            assert img is not None, 'X not contained in Y'
            if t in m:
                assert m[t] == img
            else:
                m[t] = img
                q.append(t)
    return len(set(m.values())) == len(m)


def relrank_le1(nx, Ex, ny, Ey):
    cy = canon(ny, Ey)
    if canon(nx, Ex) == cy:
        return 'eq'
    if rank(ny, Ey) == rank(nx, Ex) + 1 and embeds(nx, Ex, ny, Ey):
        return 'arc'
    for u in range(nx):
        for w in range(u + 1, nx):
            m, F, _ = fold(nx, Ex, [(u, w)])
            if canon(m, F) == cy:
                return 'pair'
    return None


if __name__ == '__main__':
    j, seed, T, G, Lm = (int(x) for x in sys.argv[1:6])
    rng = random.Random(seed)
    phij = lambda w: w if j == 0 else phij_(w)

    def phij_(w):
        for _ in range(j):
            w = phi(w)
        return w
    nB, EB = graph_of(['a', phij_('b')])
    stats = dict(X=0, J=0, Yneq=0, Ytop=0, viol=0)
    for trial in range(T):
        X0 = [rand_word(rng.randint(1, Lm), rng) for _ in range(rng.randint(1, G))]
        X = [phij_(w) for w in X0]
        nx, Ex = compact(*graph_of(X))
        if rank(nx, Ex) < 1:
            continue
        stats['X'] += 1
        seen = set()
        for u in range(nx):
            for w in range(u + 1, nx):
                m, F, _ = fold(nx, Ex, [(u, w)])
                c = canon(m, F)
                if c in seen:
                    continue
                seen.add(c)
                stats['J'] += 1
                ny, Ey = compact(*pullback(m, F, nB, EB))
                if canon(ny, Ey) == canon(nx, Ex):
                    continue
                stats['Yneq'] += 1
                if canon(ny, Ey) == canon(nB, EB):
                    stats['Ytop'] += 1
                r = relrank_le1(nx, Ex, ny, Ey)
                if r is None:
                    stats['viol'] += 1
                    print('RI-K1-VIOLATION j=%d X0=%s pair=(%d,%d)' % (j, X0, u, w), flush=True)
    print(stats)
