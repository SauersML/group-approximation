"""Exact Farkas check for the memory-r word-free polygon LP of lp_memory.py.

System (lp_memory.build):  A y + B c = e_norm,  y, c >= 0, with a column A_P per legal typed vertex polygon P
(lp_memory.polygons) and a column B_v per window v.  An integer vector z with
    z . A_P <= 0 for every polygon P,   z . B_v <= 0 for every window v,   z_norm > 0
proves that the system is infeasible (z . (A y + B c) would be both <= 0 and = z_norm > 0).  Then no legal
f^m-folded fatgraph over the rose exists at all, whatever its boundary (lp_memory.validate projects every one
to a feasible point).

z comes from the floating phase-1 duals of cg_memory.py (--dual dump): shift the type duals by -eps and the
normalisation dual by -eps (1 + max|f(x)|), which makes every polygon charge <= -2 eps and keeps every window
charge <= its old value, scale by D and round.  All checks below are then in exact integer arithmetic (float64
holding integers below 2^53).  The max over all polygons is computed by max-plus products over darts, and
--selftest compares it with brute force over lp_memory.polygons at r = 1 for random integer z.

usage: python3 verify_farkas_memory.py dump.json [--eps E] [--D D]
       python3 verify_farkas_memory.py --selftest '<phi0 json>' m
"""
import sys, json, itertools
import numpy as np
import lp_memory as LM
import lp_allwords as LA
from ffold import inv


def maxplus(A, Bm):
    n1, n2 = A.shape
    n3 = Bm.shape[1]
    out = np.full((n1, n3), -np.inf)
    if n1 == 0 or n2 == 0 or n3 == 0:
        return out
    ch = max(1, int(3e6 // max(1, n1 * n3)))
    for k0 in range(0, n2, ch):
        out = np.maximum(out, (A[:, k0:k0 + ch, None] + Bm[None, k0:k0 + ch, :]).max(axis=1))
    return out


def max_polygon_charge(TY, g, maxval, zt, zpair):
    """max over legal typed polygons P of sum_s (zt[d_s] + sign * zpair[{d_s, q_s}])."""
    N = TY.N
    LET = TY.L
    gl = sorted({g[x] for x in LET})
    gid = np.array([gl.index(g[TY.label[d]]) for d in range(N)])
    mk = np.array([k == "-" for k in TY.kind])
    fd = np.array(TY.fdart, dtype=bool)
    li = np.array([LET.index(x) for x in TY.label])
    invi = np.array([LET.index(inv(x)) for x in LET])
    V = (li[None, :] == invi[li][:, None]) & ~(mk[:, None] & mk[None, :])
    Wt = np.zeros((N, N))
    for (a, b), v in zpair.items():
        Wt[a, b] += v; Wt[b, a] -= v            # slot a -> b has sign +1 if a < b (a < b in keys)
    Wq = np.where(V, zt[:, None] + Wt, -np.inf)  # weight of slot d -> q
    M = np.full((N, N), -np.inf)                 # M[d, n] = max_q {w(d, q) : n in succ(q)}
    for q in range(N):
        for n in TY.succ[q]:
            M[:, n] = np.maximum(M[:, n], Wq[:, q])
    ok2 = (gid[:, None] != gid[None, :]) & ~(mk[:, None] & mk[None, :]) & ~(fd[:, None] & fd[None, :])
    T = np.where(ok2, M + M.T, -np.inf)
    best = {2: float(T.max())}
    blocks = {}
    for gi in range(len(gl)):
        for m in (False, True):
            idx = np.where((gid == gi) & (mk == m) & ~fd)[0]
            if len(idx):
                blocks[(gi, m)] = idx
    for kk in (3, 4):
        if kk > maxval:
            continue
        b = -np.inf
        for seq in itertools.permutations(list(blocks), kk):
            gs = [s[0] for s in seq]
            if len(set(gs)) < kk or gs[0] != min(gs) or sum(s[1] for s in seq) > 1:
                continue
            I = [blocks[s] for s in seq]
            P = M[np.ix_(I[0], I[1])]
            for j in range(1, kk):
                P = maxplus(P, M[np.ix_(I[j], I[(j + 1) % kk])])
            b = max(b, float(np.diagonal(P).max()))
        best[kk] = b
    return max(best.values()), best


def setup(phi0, m, r, maxval=None):
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    if maxval is None:
        maxval = max(2, 2 * min(gp, gn))
    TY = LM.MTypes(phi, g, r)
    return phi, g, TY, maxval


def selftest(phi0, m):
    phi, g, TY, maxval = setup(phi0, m, 1)
    polys = LM.polygons(TY, g, maxval)
    rng = np.random.default_rng(1)
    for trial in range(3):
        zt = rng.integers(-50, 50, TY.N).astype(float)
        keys = {(min(d, q), max(d, q)) for P in polys for (d, q) in P}
        zp = {k: float(rng.integers(-50, 50)) for k in keys}
        brute = max(sum(zt[d] + (zp[(d, q)] if d < q else -zp[(q, d)]) for (d, q) in P) for P in polys)
        # the DP also sees pairs absent from keys with weight 0; they belong to no polygon, so no effect
        dp, _ = max_polygon_charge(TY, g, maxval, zt, zp)
        print("selftest trial", trial, "polygons", len(polys), "brute", brute, "dp", dp,
              "OK" if brute == dp else "MISMATCH", flush=True)


def main():
    args = sys.argv[1:]
    if args[0] == "--selftest":
        selftest(json.loads(args[1]), int(args[2]))
        return
    eps, D = 1e-4, 10 ** 6
    if "--eps" in args:
        i = args.index("--eps"); eps = float(args[i + 1]); del args[i:i + 2]
    if "--D" in args:
        i = args.index("--D"); D = int(args[i + 1]); del args[i:i + 2]
    J = json.load(open(args[0]))
    phi, g, TY, maxval = setup(J["phi0"], J["power"], J["r"])
    nrows0, _, ccols = LM.build(TY, [])
    rN = J["rN"]
    assert rN == nrows0
    y = np.array(J["y"])
    N = TY.N
    Rmax = max(len(TY.R[x]) for x in TY.L)
    zf = y[:rN + 1].copy()
    zf[:N] -= eps
    zf[rN] -= eps * (1 + Rmax)
    z = np.round(zf * D)
    zt = z[:N]
    zpair = {(a, b): float(np.round(y[rw] * D)) for a, b, rw in J["prow"]}
    # windows: z . B_v = sum_rows col * z + z_norm
    wmax = max(sum(v * z[row] for row, v in col.items()) + z[rN] for col in ccols)
    pmax, best = max_polygon_charge(TY, g, maxval, zt, zpair)
    print("phi0", J["phi0"], "m", J["power"], "r", J["r"], "types", N, "windows", len(ccols), "maxval", maxval)
    print("D", D, "eps", eps, "z_norm", z[rN], "max window charge", wmax, "max polygon charge", pmax, best)
    ok = z[rN] > 0 and wmax <= 0 and pmax <= 0
    print("FARKAS", "VERIFIED" if ok else "FAILED", flush=True)


if __name__ == "__main__":
    main()
