"""Two-sided strip surgery for abelian torus covers (Z/2 dipoles), no GL2 back-substitution.

Base G = Z^2/Lambda (HNF N1,N2,C), fibre Z/2, charges at vertices 0 and g (surgery.build).
w = k v shortest lattice vector (v primitive), L = N/k, row index r(z) = det(v,z) mod L.
Cut the row circle Z/L into cyclic intervals ("pieces") of height >= l = |v|_inf; reglue each
piece P = [r1, r1+H) to a torus: a b- or c-move leaving P through its top (bottom) is redirected
by -H u (+H u), det(v,u)=1.  Fibre values are kept; the new charges are then cancelled inside
each piece along a greedy Steiner tree.  Everything is checked: commutation of the final pair,
exact ranks.  Reports, per case, exact rho, path-cut cost, best 2-cut strip cost, and the ratio
of max(rank(b''-b), rank(c''-c)) to rho and to lambda_1.
usage: python3 strips.py Nmin Nmax
"""
import sys, os
from math import gcd
from collections import deque
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'rectangle-profile-dipoles-2026-09-17'))
if os.environ.get('SURGERY_DIR'): sys.path.insert(0, os.environ['SURGERY_DIR'])
import surgery as S          # build, perms, kappa, Torus (w7-124)
import perm as P             # exact profile (numpy)

def shortest(T):
    N = T.N; best = None
    for a in range(-N, N + 1):
        for b in range(-N, N + 1):
            if (a, b) != (0, 0) and T.idx(a, b) == 0 and (best is None or abs(a) + abs(b) < abs(best[0]) + abs(best[1])):
                best = (a, b)
    return best

def frame(T):
    w = shortest(T); k = gcd(abs(w[0]), abs(w[1])); v = (w[0] // k, w[1] // k)
    m = abs(v[0]) + abs(v[1]) + 1; u = None
    for u1 in range(-m, m + 1):
        for u2 in range(-m, m + 1):
            if v[0] * u2 - v[1] * u1 == 1 and (u is None or abs(u1) + abs(u2) < abs(u[0]) + abs(u[1])): u = (u1, u2)
    return w, k, v, u

def rows(T, v, k):
    L = T.N // k
    for lam in ((T.N1, 0), (T.C, T.N2)):
        assert (v[0] * lam[1] - v[1] * lam[0]) % L == 0
    r = [0] * T.N
    for h in range(T.N):
        x, y = T.coords(h); r[h] = (v[0] * y - v[1] * x) % L
    return L, r

def reglue(T, v, u, L, r, cuts):
    """cuts: sorted list of row indices where a piece starts. Returns new base maps nb, nc and piece id."""
    N = T.N; starts = sorted(cuts); pieces = []
    for i, s in enumerate(starts):
        e = starts[(i + 1) % len(starts)]; H = (e - s) % L or L; pieces.append((s, H))
    pid = [0] * N; loc = [0] * N
    for h in range(N):
        for j, (s, H) in enumerate(pieces):
            if (r[h] - s) % L < H: pid[h] = j; loc[h] = (r[h] - s) % L
    nb = [0] * N; nc = [0] * N
    for h in range(N):
        x, y = T.coords(h); s, H = pieces[pid[h]]
        for (dx, dy, D, out) in ((1, 0, -v[1], nb), (0, 1, v[0], nc)):
            t = loc[h] + D; X, Y = x + dx, y + dy
            if t >= H: X -= H * u[0]; Y -= H * u[1]
            elif t < 0: X += H * u[0]; Y += H * u[1]
            z = T.idx(X, Y); assert pid[z] == pid[h] and loc[z] == t % H if H >= abs(D) else True
            out[h] = z
    for h in range(N): assert nb[nc[h]] == nc[nb[h]]
    return nb, nc, pieces

def cancel(N, nb, nc, beta, gamma):
    """kappa(x) = beta(x)+gamma(nb x)+gamma(x)+beta(nc x) over Z/2; cancel along greedy Steiner trees."""
    beta = beta[:]; gamma = gamma[:]
    kap = lambda x: beta[x] ^ gamma[nb[x]] ^ gamma[x] ^ beta[nc[x]]
    ib = [0] * N; ic = [0] * N
    for h in range(N): ib[nb[h]] = h; ic[nc[h]] = h
    # flipping beta[x] toggles kappa at x and at ic[x]; flipping gamma[x] toggles x and ib[x]
    adj = [[] for _ in range(N)]
    for x in range(N):
        adj[x].append((ic[x], 'b', x)); adj[ic[x]].append((x, 'b', x))
        adj[x].append((ib[x], 'g', x)); adj[ib[x]].append((x, 'g', x))
    ch = set(x for x in range(N) if kap(x))
    while ch:
        root = min(ch); tree = {root}; parent = {root: None}
        compo = {root}; dq = deque([root])
        while dq:
            x = dq.popleft()
            for (y, lab, e) in adj[x]:
                if y not in compo: compo.add(y); dq.append(y)
        todo = (set(ch) & compo) - {root}
        comp_order = [root]
        while todo:
            prev = {t: None for t in tree}; dq = deque(tree); hit = None
            while dq:
                x = dq.popleft()
                if x in todo: hit = x; break
                for (y, lab, e) in adj[x]:
                    if y not in prev: prev[y] = (x, lab, e); dq.append(y)
            if hit is None: raise RuntimeError('non-neutral piece')
            y = hit; path = []
            while y not in tree: x, lab, e = prev[y]; path.append((y, x, lab, e)); y = x
            for (y, x, lab, e) in reversed(path): tree.add(y); parent[y] = (x, lab, e); comp_order.append(y)
            todo -= tree
        val = {x: (1 if x in ch else 0) for x in tree}
        if len(set(ch) & compo) % 2: raise RuntimeError('non-neutral piece')
        for y in reversed(comp_order[1:]):
            if val[y]:
                x, lab, e = parent[y]
                if lab == 'b': beta[e] ^= 1
                else: gamma[e] ^= 1
                val[y] ^= 1; val[x] ^= 1
        assert val[root] == 0
        ch = set(x for x in range(N) if kap(x))
    return beta, gamma

def build_pair(N, nb, nc, beta, gamma):
    b = np.empty(2 * N, int); c = np.empty(2 * N, int)
    for h in range(N):
        for e in (0, 1): b[2 * h + e] = 2 * nb[h] + (e ^ beta[h]); c[2 * h + e] = 2 * nc[h] + (e ^ gamma[h])
    return b, c

def strip_cost(T, bp, cp, beta, gamma, v, u, L, r, cuts):
    nb, nc, pieces = reglue(T, v, u, L, r, cuts)
    b2f, g2f = cancel(T.N, nb, nc, beta, gamma)
    b2, c2 = build_pair(T.N, nb, nc, b2f, g2f)
    assert np.array_equal(b2[c2], c2[b2])
    return P.rk(b2, bp), P.rk(c2, cp)

def two_cuts(L, l):
    out = []
    for a in range(L):
        for b in range(a + 1, L):
            if b - a >= l and L - (b - a) >= l: out.append([a, b])
    return out

if __name__ == "__main__":
    a, b = int(sys.argv[1]), int(sys.argv[2])
    worst = {'rho': 0, 'lam': 0}; ncase = 0
    for N in range(a, b + 1):
        for N1 in range(1, N + 1):
            if N % N1: continue
            for C in range(N1):
                T = S.Torus(N1, N // N1, C)
                w, k, v, u = frame(T); lam1 = abs(w[0]) + abs(w[1]); l = max(abs(v[0]), abs(v[1]))
                L, r = rows(T, v, k)
                for g in range(1, T.N):
                    beta, gamma, gl = S.build(T, g)
                    bp, cp = (np.array(p) for p in S.perms(T, beta, gamma))
                    rho = P.profile(bp, cp)[0]
                    path = max(P.rk(np.array(S.perms(T, [0]*T.N, [0]*T.N)[0]), bp), P.rk(np.array(S.perms(T, [0]*T.N, [0]*T.N)[1]), cp))
                    best = None
                    for cuts in two_cuts(L, l):
                        rb, rc = strip_cost(T, bp, cp, beta, gamma, v, u, L, r, cuts)
                        if best is None or max(rb, rc) < best[0]: best = (max(rb, rc), rb, rc, cuts)
                    st = best[0] if best else None
                    ub = min(path, st) if st is not None else path
                    ncase += 1
                    worst['rho'] = max(worst['rho'], ub / rho)
                    if gl > lam1: worst['lam'] = max(worst['lam'], (st if st is not None else 10**9) / lam1)
                    print(N, N1, C, g, 'lam1=%d |g|=%d L=%d l=%d' % (lam1, gl, L, l), 'rho=%.3f' % rho,
                          'path=%d' % path, 'strip=', best, 'ub/rho=%.3f' % (ub / rho), flush=True)
    print('CASES', ncase, 'WORST dist/rho %.3f' % worst['rho'], 'WORST strip/lambda1 (|g|>lambda1) %.3f' % worst['lam'])
