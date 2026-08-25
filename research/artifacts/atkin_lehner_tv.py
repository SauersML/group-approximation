#!/usr/bin/env python3
"""Total-variation mismatch between the isotypic weight measures of
  (i)  the permutation representation of G' = Gamma_0(p^{2k}) mod p^{4k}
       on the far sphere X = Z/p^{2k}  (x -> [x:1])  [Moebius action], and
  (ii) the same set with the action twisted by the Atkin--Lehner involution
       Ad(g_k), g_k = [[0,p^{-k}],[-p^k,0]]  [affine action x -> (d x - c/p^{2k})/a],
and likewise for the whole sphere S = P^1(Z/p^{2k}).
Method: V = X (+) X'; End_G(V) = span of orbital matrices; centre -> isotypic
projections e_pi; w_X(pi) = tr(e_pi P_X)/|X|.  No group enumeration needed."""
import sys, itertools, numpy as np
from collections import deque

def units_generators(p, m):
    """generators of (Z/p^m)^x"""
    if p == 2:
        return [g for g in (-1 % 2**m, 5 % 2**m) if m >= 1]
    # cyclic: find a primitive root mod p^m
    n = p**m; phi = (p-1)*p**(m-1)
    fac = [q for q in range(2, phi+1) if phi % q == 0 and all(q % r for r in range(2, int(q**0.5)+1))]
    for g in range(2, n):
        if g % p == 0: continue
        if all(pow(g, phi//q, n) != 1 for q in fac):
            return [g]
    raise RuntimeError

def make_group_generators(p, k):
    N2, N4 = p**(2*k), p**(4*k)
    gens = []
    gens.append(((1, 1), (0, 1)))              # t
    gens.append(((1, 0), (N2 % N4, 1)))        # l = e_21(p^{2k})
    for u in units_generators(p, 2*k):
        uu = u % N4
        # lift u (unit mod p^{2k}) to a unit mod p^{4k}: u itself is a unit mod p^{4k} iff gcd(u,p)=1 -- yes
        uinv = pow(uu, -1, N4)
        gens.append(((uu, 0), (0, uinv)))
    return gens

def far_action(M, x, p, k):
    N2, N4 = p**(2*k), p**(4*k)
    (a, b), (c, d) = M
    num = (a*x + b) % N2; den = (c*x + d) % N2
    return (num * pow(den, -1, N2)) % N2

def far_twisted_action(M, x, p, k):
    N2, N4 = p**(2*k), p**(4*k)
    (a, b), (c, d) = M
    assert c % N2 == 0
    cq = (c // N2) % N2           # c/p^{2k} mod p^{2k}, needs c mod p^{4k}
    return ((d*x - cq) * pow(a % N2, -1, N2)) % N2

def sphere_points(p, k):
    N2 = p**(2*k)
    pts = [(x % N2, 1) for x in range(N2)] + [(1, (p*y) % N2) for y in range(p**(2*k-1))]
    return pts

def normalize(v, p, k):
    N2 = p**(2*k)
    x, y = v[0] % N2, v[1] % N2
    if x % p != 0:            # x unit -> [1 : y/x]?? keep canonical form used in sphere_points
        pass
    # canonical: if y is a unit -> (x*y^{-1}, 1); else x is a unit -> (1, y*x^{-1}) with y*x^{-1} divisible by p
    if y % p != 0:
        return ((x * pow(y, -1, N2)) % N2, 1)
    else:
        return (1, (y * pow(x, -1, N2)) % N2)

def sphere_action(M, v, p, k, twisted=False):
    N2 = p**(2*k)
    (a, b), (c, d) = M
    if twisted:
        cq = (c // N2) % N2
        a, b, c, d = d % N2, (-cq) % N2, 0, a % N2
    x, y = v
    return normalize((a*x + b*y, c*x + d*y), p, k)

def orbital_algebra(perms, n):
    """perms: list of permutations (arrays) of range(n) for generators.
    Returns basis of End_G(C^n) as list of 0/1 matrices (orbitals of G on pairs)."""
    seen = -np.ones((n, n), dtype=np.int64)
    orbitals = []
    for i in range(n):
        for j in range(n):
            if seen[i, j] >= 0: continue
            oid = len(orbitals); seen[i, j] = oid
            q = deque([(i, j)]); members = [(i, j)]
            while q:
                u, v = q.popleft()
                for s in perms:
                    a, b = s[u], s[v]
                    if seen[a, b] < 0:
                        seen[a, b] = oid; q.append((a, b)); members.append((a, b))
            Mx = np.zeros((n, n)); 
            for (u, v) in members: Mx[u, v] = 1.0
            orbitals.append(Mx)
    return orbitals

def isotypic_projections(orbs, n, rng):
    """Isotypic projections of V from a generic self-adjoint element of the
    orbital algebra: its eigenspaces are G-invariant; two eigenspaces lie in
    the same isotypic component iff some orbital maps one into the other."""
    A = sum(rng.standard_normal() * o for o in orbs); A = (A + A.T) / 2
    w, U = np.linalg.eigh(A)
    blocks = []; i = 0
    while i < n:
        j = i
        while j + 1 < n and abs(w[j+1] - w[i]) < 1e-7 * max(1.0, abs(w[i])): j += 1
        blocks.append((i, j + 1)); i = j + 1
    nb = len(blocks)
    # adjacency: block r ~ block s if some orbital has a nonzero (r,s) compression
    adj = np.zeros((nb, nb), dtype=bool)
    for o in orbs:
        T = U.T @ o @ U
        for r, (a, b) in enumerate(blocks):
            for t, (c, d) in enumerate(blocks):
                if r != t and not adj[r, t] and np.abs(T[a:b, c:d]).max() > 1e-8:
                    adj[r, t] = adj[t, r] = True
    # connected components
    comp = -np.ones(nb, dtype=int); cid = 0
    for r in range(nb):
        if comp[r] >= 0: continue
        stack = [r]; comp[r] = cid
        while stack:
            x = stack.pop()
            for y in np.nonzero(adj[x])[0]:
                if comp[y] < 0: comp[y] = cid; stack.append(y)
        cid += 1
    projs = []
    for c in range(cid):
        cols = np.concatenate([np.arange(a, b) for r, (a, b) in enumerate(blocks) if comp[r] == c])
        Ub = U[:, cols]; projs.append(Ub @ Ub.T)
    return projs, cid

def run(p, k, which, rng):
    gens = make_group_generators(p, k)
    if which == 'far':
        pts = list(range(p**(2*k)))
        act = lambda M, x: far_action(M, x, p, k)
        act2 = lambda M, x: far_twisted_action(M, x, p, k)
    else:
        pts = sphere_points(p, k)
        act = lambda M, v: sphere_action(M, v, p, k, False)
        act2 = lambda M, v: sphere_action(M, v, p, k, True)
    idx = {pt: i for i, pt in enumerate(pts)}; nX = len(pts)
    perms = []
    for M in gens:
        s1 = np.array([idx[act(M, pt)] for pt in pts])
        s2 = np.array([idx[act2(M, pt)] for pt in pts])
        assert len(set(s1)) == nX and len(set(s2)) == nX
        perms.append(np.concatenate([s1, s2 + nX]))
    n = 2 * nX
    orbs = orbital_algebra(perms, n)
    projs, zdim = isotypic_projections(orbs, n, rng)
    PX = np.zeros((n, n)); PX[:nX, :nX] = np.eye(nX)
    PY = np.eye(n) - PX
    tv = 0.0; details = []
    for e in projs:
        wx = np.trace(e @ PX) / nX; wy = np.trace(e @ PY) / nX
        tv += abs(wx - wy); details.append((round(wx, 6), round(wy, 6), int(round(np.trace(e)))))
    return tv, nX, len(orbs), zdim, details

if __name__ == '__main__':
    rng = np.random.default_rng(1)
    cases = [(2,1),(2,2),(3,1),(5,1),(7,1),(2,3),(3,2),(11,1)]
    for (p, k) in cases:
        for which in ('far', 'sphere'):
            try:
                tv, nX, m, zdim, det = run(p, k, which, rng)
                print(f"p={p} k={k} {which:6s} |X|={nX:4d} dim End_G(V)={m:4d} #isotypic={zdim:3d}  TV={tv:.6f}")
                if nX <= 16: print("   (w_X, w_X', dim isotypic):", det)
            except Exception as ex:
                print(f"p={p} k={k} {which}: ERROR {ex!r}")
        sys.stdout.flush()
