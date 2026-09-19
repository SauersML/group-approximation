"""Compute R*(k) = K * min_A max_e Pr_A[A cuts e] for k = 2, 3 by symmetric
column generation, where A ranges over folded distributions that are random
on the primaries of Had_k and e over length-one edges of {-1,1}^K.  Two
primary sets are run: all 2^k signed characters +-chi_S including chi_empty
(HHM+15 Definition 2.21/2.24, the setting of their Theorems 1.8 and 6.1) and
the 2^k - 1 nonconstant ones (the (2^k-1)-ary Had'_k).

By item 1 of hadamard-gadget-deletion-ratio-window, R*(k) is the best
deletion ratio s/c of any (c,s)-generic Had_k -> Max-2Lin(2) gadget
(HHM+15 Definition 2.16).  Known values: k = 3 gives 11/8 (HHM+15 Theorem
1.8, optimal gadget), which this script reproduces as a check of the minimax
identity.  The adversary side is symmetrised over the affine group AGL(k,2)
acting on the coordinates together with x -> -x, so the master LP has one
row per edge orbit and one equality per orbit of primary patterns; columns
are folded functions, priced exactly by a MILP (min weighted cut with the
primaries pinned and folding built in).  The final pricing round proves no
column has negative reduced cost, so the LP value is R*(k)/K exactly up to
floating tolerance.
"""
import itertools
import sys
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds


def setup(k, first=0):
    K = 1 << k
    N = 1 << K
    full = N - 1
    prim = []
    for a in range(first, K):
        prim.append(sum(1 << i for i in range(K) if bin(a & i).count("1") % 2))
    # affine permutations of coordinates
    mats = []
    for bits in itertools.product([0, 1], repeat=k * k):
        M = np.array(bits).reshape(k, k)
        cols = [int("".join(map(str, M[:, c][::-1])), 2) for c in range(k)]
        span = {0}
        for c in cols:
            span |= {s ^ c for s in span}
        if len(span) == K:
            mats.append(cols)
    perms = []
    for cols in mats:
        for v in range(K):
            p = []
            for i in range(K):
                img = v
                for c in range(k):
                    if (i >> c) & 1:
                        img ^= cols[c]
                p.append(img)
            perms.append(p)

    def act(p, x, neg):
        y = 0
        for i in range(K):
            if (x >> i) & 1:
                y |= 1 << p[i]
        return y ^ full if neg else y

    # edges (x, x^(1<<j)) with bit j of x zero
    edges = [(x, x ^ (1 << j)) for x in range(N) for j in range(K) if not (x >> j) & 1]
    eidx = {frozenset(e): n for n, e in enumerate(edges)}
    orb = [-1] * len(edges)
    norb = 0
    for n, (x, y) in enumerate(edges):
        if orb[n] >= 0:
            continue
        for p in perms:
            for neg in (False, True):
                m = eidx[frozenset((act(p, x, neg), act(p, y, neg)))]
                orb[m] = norb
        norb += 1
    osize = np.bincount(orb, minlength=norb)
    # primary patterns xi in {0,1}^(K-1) (bit a-1 set <=> xi_a = -1); group action
    pidx = {m: a for a, m in enumerate(prim)}

    def pat_act(p, neg, xi):
        # (g.f)(chi_a) = f(g^-1 chi_a); we use all g, so act by g directly
        out = 0
        for a, m in enumerate(prim):
            gm = act(p, m, neg)
            if gm in pidx:
                val = (xi >> pidx[gm]) & 1
            else:
                val = 1 ^ ((xi >> pidx[gm ^ full]) & 1)
            out |= val << a
        return out
    npat = 1 << len(prim)
    porb = [-1] * npat
    reps = []
    for xi in range(npat):
        if porb[xi] >= 0:
            continue
        for p in perms:
            for neg in (False, True):
                porb[pat_act(p, neg, xi)] = len(reps)
        reps.append(xi)
    psize = np.bincount(porb, minlength=len(reps))
    return dict(K=K, N=N, full=full, prim=prim, edges=edges, orb=np.array(orb),
                norb=norb, osize=osize, reps=reps, psize=psize, npat=npat)


def price(S, w, xi):
    """min over folded f with f(chi_a) = xi_a of sum_e w_e cut_e(f)."""
    K, N, full, edges = S["K"], S["N"], S["full"], S["edges"]
    canon = {}
    reps = [x for x in range(N) if x < (x ^ full)]
    for r, x in enumerate(reps):
        canon[x] = (r, 0)
        canon[x ^ full] = (r, 1)
    nb, ne = len(reps), len(edges)
    c = np.r_[np.zeros(nb), w]
    rows, lo, hi = [], [], []
    for n, (x, y) in enumerate(edges):
        (rx, sx), (ry, sy) = canon[x], canon[y]
        par = sx ^ sy
        r1 = np.zeros(nb + ne); r2 = np.zeros(nb + ne)
        r1[nb + n] = 1; r2[nb + n] = 1
        if par == 0:     # cut iff b_rx != b_ry
            r1[rx] -= 1; r1[ry] += 1; r2[rx] += 1; r2[ry] -= 1
            rows += [r1, r2]; lo += [0, 0]
        else:            # cut iff b_rx == b_ry
            r1[rx] += 1; r1[ry] += 1; r2[rx] -= 1; r2[ry] -= 1
            rows += [r1, r2]; lo += [1, -1]
        hi += [np.inf, np.inf]
    lb = np.zeros(nb + ne); ub = np.ones(nb + ne)
    for a, m in enumerate(S["prim"]):
        want = (xi >> a) & 1          # 1 <=> f(chi_a) = -1
        r, s = canon[m]
        val = want ^ s
        lb[r] = ub[r] = val
    integ = np.r_[np.ones(nb), np.zeros(ne)]
    res = milp(c, constraints=LinearConstraint(np.array(rows), lo, hi),
               integrality=integ, bounds=Bounds(lb, ub))
    b = np.round(res.x[:nb]).astype(int)
    cut = np.zeros(ne)
    for n, (x, y) in enumerate(edges):
        (rx, sx), (ry, sy) = canon[x], canon[y]
        cut[n] = (b[rx] ^ sx) != (b[ry] ^ sy)
    return float(cut @ w), cut


def solve(k, first=0, iters=400):
    S = setup(k, first)
    K, orb, norb, osize = S["K"], S["orb"], S["norb"], S["osize"]
    nq = len(S["reps"])
    name = "Had_k (2^k primaries, Def 2.24)" if first == 0 else "Had'_k (2^k-1 primaries)"
    print(f"k={k} {name}: {len(S['edges'])} edges in {norb} orbits, {nq} pattern orbits")
    cols = []   # (q, orbit-average cut vector)

    def orbavg(cut):
        return np.bincount(orb, weights=cut, minlength=norb) / osize
    w0 = np.ones(len(S["edges"])) / len(S["edges"])
    for q, xi in enumerate(S["reps"]):
        cols.append((q, orbavg(price(S, w0, xi)[1])))
    for it in range(iters):
        M = len(cols)
        cvec = np.r_[np.zeros(M), 1.0]
        Aub = np.zeros((norb, M + 1)); Aub[:, M] = -1
        Aeq = np.zeros((nq, M + 1))
        for c, (q, a) in enumerate(cols):
            Aub[:, c] = a
            Aeq[q, c] = 1
        beq = S["psize"] / S["npat"]
        res = linprog(cvec, A_ub=Aub, b_ub=np.zeros(norb), A_eq=Aeq, b_eq=beq,
                      bounds=[(0, None)] * M + [(None, None)], method="highs")
        lam = -res.ineqlin.marginals
        nu = res.eqlin.marginals
        wE = lam[orb] / osize[orb]
        added = 0
        for q, xi in enumerate(S["reps"]):
            v, cut = price(S, wE, xi)
            if v < nu[q] - 1e-9:
                cols.append((q, orbavg(cut))); added += 1
        if added == 0:
            print(f"  converged after {it} rounds: R*({k}) = K*z = {K * res.fun:.6f}")
            return K * res.fun
    print("  not converged", K * res.fun)
    return K * res.fun


if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]] or [2, 3]
    for k in ks:
        for first in (0, 1):
            solve(k, first)
