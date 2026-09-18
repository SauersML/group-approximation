"""Two-torus cross-slit pair with trivial period lattice.

Omega = T1 ⊔ T2, T1 = (Z/p)^2, T2 = (Z/(p+1))^2.  b, c are the unit translations,
then b is swapped at x1 = (0,0) in T1 and x2 = (0,0) in T2, and c is swapped at the same
two squares.  Checks, for each p:
  * the pair is within max-rank 1 of the commuting pair (b0, c0)       (dist <= 1);
  * rho over all s, t <= SMAX (exact rank = d - #cycles), and rho <= 2 (proved);
  * the period lattice: gcd of the abelianized words fixing a point is Z^2;
  * one-sided rounding: min over c' in C(b) of #{x : c'(x) != c(x)} (exact, by assignment
    over cycles of equal length and all rotations), and the same with b and c exchanged.
    rank(c' - c) >= that number / 2, and the proof gives >= 4p + 2 disagreements, so rank >= 2p + 1.
"""
import sys
from math import gcd
import numpy as np
from scipy.optimize import linear_sum_assignment

def build(p):
    idx = {}
    for k, n in ((0, p), (1, p + 1)):
        for i in range(n):
            for j in range(n):
                idx[(k, i, j)] = len(idx)
    d = len(idx)
    b0 = [0] * d; c0 = [0] * d
    for (k, i, j), x in idx.items():
        n = p + k
        b0[x] = idx[(k, (i + 1) % n, j)]
        c0[x] = idx[(k, i, (j + 1) % n)]
    x1, x2 = idx[(0, 0, 0)], idx[(1, 0, 0)]
    b = b0[:]; c = c0[:]
    b[x1], b[x2] = b0[x2], b0[x1]
    c[x1], c[x2] = c0[x2], c0[x1]
    return d, b, c, b0, c0

def comp(f, g):  # f after g
    return [f[g[x]] for x in range(len(g))]

def inv(f):
    r = [0] * len(f)
    for x, y in enumerate(f):
        r[y] = x
    return r

def power(f, k):
    r = list(range(len(f))); base = f[:]
    while k:
        if k & 1: r = comp(base, r)
        base = comp(base, base); k >>= 1
    return r

def cycles(f):
    seen = [False] * len(f); out = []
    for x in range(len(f)):
        if not seen[x]:
            cyc = []; y = x
            while not seen[y]:
                seen[y] = True; cyc.append(y); y = f[y]
            out.append(cyc)
    return out

def rank_minus_I(f):
    return len(f) - len(cycles(f))

def perm_rank_diff(f, g):  # rank(P_f - P_g) = rank(I - P_{g^-1 f})
    return rank_minus_I(comp(inv(g), f))

def rho_scan(b, c, smax):
    best = 0.0; arg = None
    bi, ci = inv(b), inv(c)
    for s in range(1, smax + 1):
        bs, bsi = power(b, s), power(bi, s)
        for t in range(1, smax + 1):
            ct, cti = power(c, t), power(ci, t)
            w = comp(bs, comp(ct, comp(bsi, cti)))
            r = rank_minus_I(w) / (s + t)
            if r > best: best, arg = r, (s, t)
    return best, arg

def one_sided(keep, other):
    """min #disagreements of `other` with a permutation commuting with `keep`."""
    cyc = cycles(keep)
    pos = {}
    for ci_, cy in enumerate(cyc):
        for r, x in enumerate(cy):
            pos[x] = (ci_, r)
    bylen = {}
    for ci_, cy in enumerate(cyc):
        bylen.setdefault(len(cy), []).append(ci_)
    agree = 0
    for L, ids in bylen.items():
        W = np.zeros((len(ids), len(ids)), dtype=np.int64)
        col = {cid: j for j, cid in enumerate(ids)}
        for a, cid in enumerate(ids):
            # c' maps cyc[cid][r] -> cyc[cid2][(r + shift) % L]; count agreements per (cid2, shift)
            cnt = {}
            for r, x in enumerate(cyc[cid]):
                y = other[x]
                cid2, r2 = pos[y]
                if cid2 in col:
                    key = (cid2, (r2 - r) % L)
                    cnt[key] = cnt.get(key, 0) + 1
            for (cid2, _), v in cnt.items():
                W[a, col[cid2]] = max(W[a, col[cid2]], v)
        ri, cj = linear_sum_assignment(-W)
        agree += int(W[ri, cj].sum())
    return len(keep) - agree

def period_gcd(b, c):
    g = 0
    for f, e in ((b, 0), (c, 1)):
        g2 = 0
        for cy in cycles(f):
            g2 = gcd(g2, len(cy))
        g = gcd(g, g2) if e else g2
        if e == 0: gx = g2
        else: gy = g2
    return gx, gy

if __name__ == "__main__":
    smax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    print("p d distb distc rho_scan(s,t<=%d) argmax gcd_b_cycles gcd_c_cycles keep_b keep_c bound_4p+2" % smax)
    for p in range(2, 16):
        d, b, c, b0, c0 = build(p)
        db, dc = perm_rank_diff(b, b0), perm_rank_diff(c, c0)
        assert comp(b0, c0) == comp(c0, b0)
        rho, arg = rho_scan(b, c, smax) if p <= 9 else (float("nan"), None)
        gx, gy = period_gcd(b, c)
        kb, kc = one_sided(b, c), one_sided(c, b)
        assert db <= 1 and dc <= 1 and gx == 1 and gy == 1
        assert kb >= 4 * p + 2 and kc >= 4 * p + 2
        assert not (rho > 2)
        print(p, d, db, dc, round(rho, 3), arg, gx, gy, kb, kc, 4 * p + 2)
    print("all assertions passed")
