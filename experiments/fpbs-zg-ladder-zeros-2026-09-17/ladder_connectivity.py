"""Exact walk-averaged connection polynomials a_(n,R)(z) on G = T_3 box K_2.

G is the Cayley graph of (Z/2*Z/2*Z/2) x Z/2 with its 4 standard involutions.
Vertices (u,i), u in T_3, i in {0,1}.  Root o=(r,0).  Ball B_R: (u,0) with
d(u)<=R and (u,1) with d(u)<=R-1 (induced subgraph).

Exactness.  Removing a pair {(u,0),(u,1)} disconnects G, so every side subtree
hanging off the tree geodesic r=v_0..v_k is a two-terminal gadget that only
matters through whether it joins its two terminals.  Gadget of a child w at
depth d contributes h(d)=z^2 g(d), with g(d)=1-(1-z)(1-h(d+1))^2 for d<=R-1
and h(d)=0 for d>=R (the bottom vertex is outside the ball).  The geodesic
strip is then a ladder with effective rungs r_j=1-(1-z)(1-h(j+1))^(s_j),
processed by a 3-state transfer (S1 both terminals joined to o, S2 top only,
S3 bottom only; "neither" is absorbing zero because o lies behind the pair).
Every quantity is a polynomial identity in z, so it holds for complex z.
"""
import numpy as np


def gadgets(z, R, dmax):
    """h[d] for d=0..dmax+1 (complex arrays)."""
    h = [np.zeros_like(z) for _ in range(dmax + 2)]
    # g(d) needs h(d+1); iterate from the deepest relevant depth
    hd1 = np.zeros_like(z)  # h(R)=0
    vals = {}
    for d in range(R - 1, -1, -1):
        g = 1 - (1 - z) * (1 - hd1) ** 2
        hd1 = z * z * g
        if d <= dmax + 1:
            vals[d] = hd1
    for d in range(dmax + 2):
        h[d] = vals.get(d, np.zeros_like(z))
    return h


def step(state, z, r):
    s1, s2, s3 = state
    a = z * (1 - z)
    n1 = s1 * (z * z + 2 * a * r) + (s2 + s3) * z * r
    n2 = s1 * a * (1 - r) + s2 * z * (1 - r)
    n3 = s1 * a * (1 - r) + s3 * z * (1 - r)
    return (n1, n2, n3)


def taus(z, R, kmax):
    """tau[k][i] = P_z(o <-> (v_k,i) inside B_R), k=0..kmax (kmax<=R)."""
    h = gadgets(z, R, kmax + 1)
    one = np.ones_like(z)
    rung = lambda j, s: (1 - (1 - z) * (1 - h[j + 1]) ** s) if j <= R - 1 else None
    out = []
    # k = 0
    r0 = rung(0, 3)
    out.append((one, r0))
    if kmax == 0:
        return out
    r0 = rung(0, 2)
    state = (r0, 1 - r0, 0 * z)  # prefix after rung 0 (k>=1 geometry)
    for k in range(1, kmax + 1):
        if k <= R - 1:
            fin = step(state, z, rung(k, 2))
            out.append((fin[0] + fin[1], fin[0] + fin[2]))
            state = step(state, z, rung(k, 1))
        else:  # k == R: only the top vertex is in the ball
            s1, s2, _ = state
            out.append((z * (s1 + s2), None))
    return out


def walk_law(n):
    """q[k][i] = P(SRW_n at tree distance k, level i) on T_3 box K_2."""
    q = np.zeros((n + 2, 2))
    q[0, 0] = 1.0
    for _ in range(n):
        nq = np.zeros_like(q)
        nq[1, :] += 0.75 * q[0, :]
        nq[0, ::-1] += 0.25 * q[0, :]
        nq[2:, :] += 0.5 * q[1:-1, :]
        # backward and level flip from k>=1
        nq[0:-1, :] += 0.25 * q[1:, :]
        nq[1:, ::-1] += 0.25 * q[1:, :]
        q = nq
    return q


def a_nR(z, n, R):
    q = walk_law(n)
    t = taus(z, R, n)
    s = np.zeros_like(z)
    for k in range(n + 1):
        s = s + q[k, 0] * t[k][0]
        if q[k, 1] != 0:
            s = s + q[k, 1] * t[k][1]
    return s
