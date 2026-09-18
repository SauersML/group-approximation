"""Exact Farkas vector for the memory-r word-free LP (optionally masked) from ANY floating dual vector, by the
dart shift.  System (lp_memory.build): A y + B c = e_norm, y, c >= 0 (masked: only windows over the mask).
1. z = round(D * y) on type and pair rows (integers); types of unmasked windows get z = -BIG (their rows carry no
   window column in the masked system, so their dual is free); a pair row {d, q} with d live and q dead gets
   -BIG/2 on the live slot d -> q and +BIG/2 on q -> d.
2. For each dart d, R_d = max(0, max_k ceil(max{charge(P) : P a k-gon through d} / k)), exact integer max-plus
   (charge(P) = sum over slots (d, q) of z_d + sign z_{dq}).  With z'_d = z_d - R_d every polygon has
   charge'(P) <= charge(P) - |P| max_{d in P} ... <= 0, since the darts of P are distinct.
3. z'_norm = min over (masked) windows v of -(B_v restricted to the other rows) . z'.  Then every window
   charge is <= 0, and if z'_norm > 0, z' is a Farkas vector: the system is infeasible.
4. Independent re-check: verify_farkas_memory.max_polygon_charge(z') <= 0 and the window charges, exactly.
Infeasible means: no legal f^m-folded fatgraph over the rose (with d^- words over the mask), any boundary.
usage: python3 farkas_rho.py dump.json [--D D] [--key y|y_rho] [--mask LETTERS] [--save cert.json]
       python3 farkas_rho.py cert.json          (compact integer certificate: rows zrows, pairs zpairs)
A certificate with a "live" window list (cg_masked.py --propwin) is re-checked in two exact steps: the masked
support propagation of sp_mask.py is re-run and must leave only live windows, and z' must be a Farkas vector of
the LP on the live windows.
"""
import sys, json, itertools
import numpy as np
import lp_memory as LM
import verify_farkas_memory as VF
from ffold import inv


def dart_max_charge(TY, g, zt, zpair):
    """exact per-dart max over k-gons through d of charge, for k = 2, 3, 4 (integer-valued float64 arrays)."""
    N = TY.N; LET = TY.L
    gl = sorted({g[x] for x in LET})
    gid = np.array([gl.index(g[TY.label[d]]) for d in range(N)])
    mk = np.array([k == "-" for k in TY.kind]); fd = np.array(TY.fdart, dtype=bool)
    li = np.array([LET.index(x) for x in TY.label]); invi = np.array([LET.index(inv(x)) for x in LET])
    V = (li[None, :] == invi[li][:, None]) & ~(mk[:, None] & mk[None, :])
    Wt = np.zeros((N, N))
    for (a, b), v in zpair.items():
        Wt[a, b] += v; Wt[b, a] -= v
    Wq = np.where(V, zt[:, None] + Wt, -np.inf)
    M = np.full((N, N), -np.inf)
    for q in range(N):
        for n in TY.succ[q]:
            M[:, n] = np.maximum(M[:, n], Wq[:, q])
    ok2 = (gid[:, None] != gid[None, :]) & ~(mk[:, None] & mk[None, :]) & ~(fd[:, None] & fd[None, :])
    out = {2: np.where(ok2, M + M.T, -np.inf).max(axis=1), 3: np.full(N, -np.inf), 4: np.full(N, -np.inf)}
    blocks = {}
    for gi in range(len(gl)):
        for m in (False, True):
            idx = np.where((gid == gi) & (mk == m) & ~fd)[0]
            if len(idx):
                blocks[(gi, m)] = idx
    for kk in (3, 4):
        for seq in itertools.permutations(list(blocks), kk):
            gs = [s[0] for s in seq]
            if len(set(gs)) < kk or gs[0] != min(gs) or sum(s[1] for s in seq) > 1:
                continue
            I = [blocks[s] for s in seq]
            Ms = [M[np.ix_(I[j], I[(j + 1) % kk])] for j in range(kk)]
            for j in range(kk):
                P = Ms[j]
                for t in range(1, kk):
                    P = VF.maxplus(P, Ms[(j + t) % kk])
                out[kk][I[j]] = np.maximum(out[kk][I[j]], np.diagonal(P))
    return out


def main():
    args = sys.argv[1:]
    D, key, mask = 10 ** 6, "y", None
    if "--save" in args:
        i = args.index("--save"); del args[i:i + 2]
    for opt in ("--D", "--key", "--mask"):
        if opt in args:
            i = args.index(opt); val = args[i + 1]; del args[i:i + 2]
            if opt == "--D": D = int(val)
            elif opt == "--key": key = val
            else: mask = val
    J = json.load(open(args[0]))
    if mask is None:
        mask = J.get("mask")
    phi, g, TY, maxval = VF.setup(J["phi0"], J["power"], J["r"])
    assert maxval == 4
    N = TY.N
    nrows0, _, ccols = LM.build(TY, [])
    rN = J["rN"]; assert rN == nrows0
    if "zrows" in J:                 # compact integer certificate (written by --save)
        D = int(J["D"])
    live = np.ones(len(TY.windows), dtype=bool) if not mask else np.array([set(v) <= set(mask) for v in TY.windows])
    if J.get("live"):
        # LP on the windows surviving exact support propagation (cg_masked.py --live); see sp_mask_sweep logs
        live &= np.array(["".join(v) in set(J["live"]) for v in TY.windows])
        assert int(live.sum()) == len(set(J["live"]))
        if "--no-prop-check" not in sys.argv:
            # re-run the exact masked support propagation: every window outside J["live"] must be forced to 0
            import sp_mask as SP
            wmask = [set(v) <= set(mask) for v in TY.windows] if mask else None
            wp, _ = SP.propagate(TY, g, 4, log=lambda *a, **k: None, wmask=wmask)
            surv = {"".join(v) for j, v in enumerate(TY.windows) if wp[j]}
            assert surv <= set(J["live"]), surv - set(J["live"])
            print("propagation re-check: %d surviving windows, all in the live list" % len(surv), flush=True)
    dead = ~live[np.array(TY.cw)]
    BIG = float(10 ** 12)
    if "zrows" in J:
        z = np.array(J["zrows"], dtype=float)
        zpair = {(a, b): float(v) for a, b, v in J["zpairs"]}
    else:
        y = np.array(J[key])
        z = np.round(y[:rN] * D)
        zpair = {(a, b): float(np.round(y[rw] * D)) for a, b, rw in J["prow"]}
        zpair = {k: v for k, v in zpair.items() if v != 0}
    if "--save" in sys.argv:
        out = sys.argv[sys.argv.index("--save") + 1]
        json.dump({"phi0": J["phi0"], "power": J["power"], "r": J["r"], "mask": mask, "live": J.get("live"), "rN": rN, "D": D,
                   "zrows": [int(v) for v in z], "zpairs": [[int(a), int(b), int(v)] for (a, b), v in zpair.items()]},
                  open(out, "w"))
    z[:N][dead] = -BIG
    # a slot d -> q with d alive and q dead: its pair row {d, q} forces it to 0 (the reverse slot q -> d lies on a
    # polygon through the dead type q), so give the alive side -BIG/2 and the dead side +BIG/2 (net -BIG/2)
    LET = TY.L
    li = np.array([LET.index(x) for x in TY.label]); invi = np.array([LET.index(inv(x)) for x in LET])
    mk = np.array([k == "-" for k in TY.kind])
    V = (li[None, :] == invi[li][:, None]) & ~(mk[:, None] & mk[None, :])
    for d, q in zip(*np.where(V & ~dead[:, None] & dead[None, :])):
        d, q = int(d), int(q)
        key2 = (min(d, q), max(d, q))
        zpair[key2] = -BIG / 2 if d < q else BIG / 2
    assert max(abs(z).max(), max([abs(v) for v in zpair.values()] + [0])) * 8 < 2 ** 52
    mc = dart_max_charge(TY, g, z[:N], zpair)
    R = np.zeros(N)
    for k in (2, 3, 4):
        R = np.maximum(R, np.ceil(np.maximum(mc[k], -BIG) / k))
    zp = z.copy(); zp[:N] -= R
    wch = [sum(v * zp[row] for row, v in col.items()) for j, col in enumerate(ccols) if live[j]]
    znorm = -max(wch)
    pmax, best = VF.max_polygon_charge(TY, g, 4, zp[:N], zpair)
    wmax = max(w + znorm for w in wch)
    print("phi0", J["phi0"], "m", J["power"], "r", J["r"], "mask", mask, "types", N, "dead types", int(dead.sum()),
          "windows", int(live.sum()), "D", D, "key", key)
    print("shift: darts with R_d > 0:", int((R > 0).sum()), "max R", float(R.max()))
    print("z'_norm", znorm, "(/D = %.6g)" % (znorm / D), "max window charge", wmax, "max polygon charge", pmax, best)
    ok = znorm > 0 and wmax <= 0 and pmax <= 0
    print("FARKAS", "VERIFIED" if ok else "FAILED", flush=True)
    if ok and "--out" not in sys.argv:
        pass


if __name__ == "__main__":
    main()
