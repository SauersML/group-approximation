"""Column generation for the full memory-r word-free LP (lp_memory.py), seeded with every 2-gon and 3-gon.
Exact support propagation (support_propagation_memory.propagate) first removes slots and windows that are zero
in every feasible point; the master then starts with all 2- and 3-gons on surviving slots, and 4-gons are
priced exactly by min-plus products (cg_memory.CGM.price).  IPM master (cg_memory), Lagrangian bounds of
cg_memory.  --load dump.json re-seeds the columns of an earlier run (checkpointing across time limits).
usage: python3 cg_full.py '<phi0 json>' m r [--prune-seed] [--cache prop.npz] [--kcol N] [--tl TOTAL_SEC] [--dual out.json] [--load dump.json]
"""
import sys, json, time, os, itertools
import numpy as np
import cg_memory as CG, lp_memory as LM, lp_allwords as LA, sp_mask as SP
import cg_masked as CM

_solve = CM.CGMask.solve_master


def _solve_cd(self):
    """master solve that also records the column reduced costs (for checkpoint pruning)"""
    res = _solve(self)
    res.cd = np.array(self.h.getSolution().col_dual)
    return res


CM.CGMask.solve_master = _solve_cd


class CGDiv(CM.CGMask):
    """CGMask with diversified pricing (CG_DIV=1): besides the kcol most negative polygons it adds, for every
    gate sequence and every dart d of the first and third positions, the most negative polygon through d
    (exact min-plus argmins).  Pricing stays exact; only the choice of added columns changes."""

    def price(self, res, phase, kcol):
        N = self.N
        base, C, Q = self.slot_costs(res, phase)
        cand = []
        T = C + C.T + base
        ok = (self.gid[:, None] != self.gid[None, :]) & ~(self.mk[:, None] & self.mk[None, :]) \
            & ~(self.fd[:, None] & self.fd[None, :])
        T = np.where(ok, T, np.inf)
        del ok
        best2 = float(T.min())
        rows = np.arange(N); am = T.argmin(axis=1); vm = T[rows, am]
        for d1 in np.where(vm < -1e-9)[0]:
            cand.append((float(vm[d1]), [int(d1), int(am[d1])], True))
        Tu = np.where(np.triu(np.ones((N, N), dtype=bool), 1), T, np.inf)
        flat = Tu.ravel()
        k = min(kcol, int(np.sum(flat < -1e-9)))
        if k > 0:
            for t in np.argpartition(flat, k - 1)[:k]:
                d1, d2 = divmod(int(t), N)
                cand.append((float(flat[t]), [d1, d2], False))
        del T, Tu, flat
        bestk = {2: best2}
        keys = list(self.blocks)
        for kk in (3, 4):
            bk = np.inf
            for seq in itertools.permutations(keys, kk):
                gs = [x[0] for x in seq]
                if len(set(gs)) < kk or gs[0] != min(gs) or sum(x[1] for x in seq) > 1:
                    continue
                I = [self.blocks[x] for x in seq]
                M12, a2 = CG.minplus(C[np.ix_(I[0], I[1])], C[np.ix_(I[1], I[2])])
                if kk == 3:
                    T = M12 + C[np.ix_(I[2], I[0])].T + base
                    a4 = None
                else:
                    M34, a4 = CG.minplus(C[np.ix_(I[2], I[3])], C[np.ix_(I[3], I[0])])
                    T = M12 + M34.T + base
                if T.size == 0:
                    continue
                bk = min(bk, float(T.min()))
                n3 = T.shape[1]

                def mk(i1, i3):
                    d1, d3 = int(I[0][i1]), int(I[2][i3])
                    d2 = int(I[1][a2[i1, i3]])
                    return [d1, d2, d3] if kk == 3 else [d1, d2, d3, int(I[3][a4[i3, i1]])]
                flat = T.ravel()
                kn = min(kcol // 4 + 1, int(np.sum(flat < -1e-9)))
                if kn > 0:
                    for t in np.argpartition(flat, kn - 1)[:kn]:
                        i1, i3 = divmod(int(t), n3)
                        cand.append((float(flat[t]), mk(i1, i3), False))
                r1 = T.argmin(axis=1)
                for i1 in np.where(T[np.arange(T.shape[0]), r1] < -1e-9)[0]:
                    cand.append((float(T[i1, r1[i1]]), mk(i1, int(r1[i1])), True))
                c3 = T.argmin(axis=0)
                for i3 in np.where(T[c3, np.arange(n3)] < -1e-9)[0]:
                    cand.append((float(T[c3[i3], i3]), mk(int(c3[i3]), i3), True))
            bestk[kk] = bk
        glob = sorted([z for z in cand if not z[2]], key=lambda z: z[0])[:kcol]
        div = [z for z in cand if z[2]]
        Ps = []
        for val, ds, _ in glob + div:
            k = len(ds)
            sl = [(ds[j], int(Q[ds[j], ds[(j + 1) % k]])) for j in range(k)]
            i = min(range(k), key=lambda j: sl[j][0])
            Ps.append(tuple(sl[i:] + sl[:i]))
        added = self.add_cols(Ps)
        return min(bestk.values()), added, bestk


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--kcol", "--tl", "--seed-sample"):
        if key in args:
            i = args.index(key); opts[key] = int(args[i + 1]); del args[i:i + 2]
    out = load = None
    if "--dual" in args:
        i = args.index("--dual"); out = args[i + 1]; del args[i:i + 2]
    if "--load" in args:
        i = args.index("--load"); load = args[i + 1]; del args[i:i + 2]
    phi0 = json.loads(args[0]); m = int(args[1]); r = int(args[2])
    phi = LA.power(phi0, m); g = LA.gates(phi)
    TY = LM.MTypes(phi, g, r)
    t0 = time.time()
    cache = None
    if "--cache" in args:
        i = args.index("--cache"); cache = args[i + 1]; del args[i:i + 2]
    import os
    if cache and os.path.exists(cache):
        Z = np.load(cache)
        walive, S = Z["walive"], np.unpackbits(Z["S"])[:TY.N * TY.N].reshape(TY.N, TY.N).astype(bool)
    else:
        walive, S = SP.propagate(TY, g, 4, log=lambda *a, **k: None)
        if cache:
            np.savez_compressed(cache, walive=walive, S=np.packbits(S.ravel()))
    print("phi0", phi0, "m", m, "r", r, "windows alive", int(walive.sum()), "slots", int(S.sum()),
          "t %.0f" % (time.time() - t0), flush=True)
    if load:
        L = json.load(open(load))
        init = [tuple(tuple(sl) for sl in P) for P in L["columns"]]
        if L.get("colx") is not None:
            # keep the columns in use or with small reduced cost (checkpoint pruning)
            thr = float(os.environ.get("CG_RCKEEP", "0.05"))
            init = [P for P, xv, rc in zip(init, L["colx"], L["colrc"]) if xv > 1e-9 or rc < thr]
        print("loaded", len(L["columns"]), "columns, kept", len(init), flush=True)
    else:
        sc = cache + ".seeds.npy" if cache else None
        if sc and os.path.exists(sc):
            A = np.load(sc)   # rows: k, d1, q1, ..., d3, q3 (padded with -1)
            init = [tuple((int(a[1 + 2 * i]), int(a[2 + 2 * i])) for i in range(int(a[0]))) for a in A]
            print("seed polygons (k<=3) from cache", len(init), flush=True)
        else:
            polys = LM.polygons(TY, g, 3)
            init = [P for P in polys if all(S[d, q] for d, q in P)]
            print("seed polygons (k<=3)", len(polys), "on surviving slots", len(init), "t %.0f" % (time.time() - t0),
                  flush=True)
            if sc:
                A = -np.ones((len(init), 7), dtype=np.int32)
                for i, P in enumerate(init):
                    A[i, 0] = len(P)
                    for j, (d, q) in enumerate(P):
                        A[i, 1 + 2 * j], A[i, 2 + 2 * j] = d, q
                np.save(sc, A)
                if "--seeds-only" in sys.argv:
                    return
    if "--seed-sample" in sys.argv and not load:
        ns = int(sys.argv[sys.argv.index("--seed-sample") + 1])
        rng = np.random.default_rng(0)
        if ns < len(init):
            init = [init[i] for i in sorted(rng.choice(len(init), ns, replace=False))]
        print("seed sample", len(init), flush=True)
    if "--prune-seed" in sys.argv:
        # one phase-1 master solve on the seeds; keep the columns in use or with reduced cost < 0.05
        pre = CM.CGMask(phi, g, TY, 4); pre.restrict(S, walive); pre.init_master(); pre.add_cols(init)
        r0 = pre.solve_master()
        cd = np.array(pre.h.getSolution().col_dual)
        keep = [P for P, j in zip(pre.cols, pre.colidx) if r0.x[j] > 1e-6 or cd[j] < 0.05]
        print("seed pruning: master obj %.6f" % r0.fun, "kept", len(keep), "of", len(init),
              "t %.0f" % (time.time() - t0), flush=True)
        init = keep
        del pre
        if out:
            json.dump({"phi0": phi0, "power": m, "r": r,
                       "columns": [[[int(d), int(q)] for d, q in P] for P in init]}, open(out + ".seed.json", "w"))
    cg = (CGDiv if os.environ.get("CG_DIV") else CM.CGMask)(phi, g, TY, 4)
    cg.restrict(S, walive)
    budget = opts.get("--tl", 1100)
    val, res = cg.run(opts.get("--kcol", 3000), max(60, budget - (time.time() - t0)), init=init)
    print("RESULT", val, flush=True)
    if res is not None and hasattr(res, "x"):
        flow = {"".join(v): round(float(res.x[j]), 6) for j, v in enumerate(TY.windows) if res.x[j] > 1e-9}
        print("window flow", flow, flush=True)
    if out:
        cd = np.array(res.cd) if res is not None and hasattr(res, "cd") else np.zeros(len(res.x) if res is not None else 0)
        json.dump({"phi0": phi0, "power": m, "r": r, "val": str(val),
                   "columns": [[[int(d), int(q)] for d, q in P] for P in cg.cols],
                   "phase": cg.phase, "obj": float(res.fun) if res is not None else None,
                   # columns added after the last master solve have no value yet: x = 0, rc = -1 (kept)
                   "colx": [float(res.x[j]) if j < len(res.x) else 0.0 for j in cg.colidx] if res is not None else None,
                   "colrc": [float(cd[j]) if j < len(res.x) else -1.0 for j in cg.colidx] if res is not None else None,
                   "rN": int(cg.rN), "y": [float(v) for v in res.y] if res is not None else None,
                   "rho_lb": float(cg.best_rho[0]) if hasattr(cg, "best_rho") else None,
                   "y_rho": [float(v) for v in cg.best_rho[1]] if hasattr(cg, "best_rho") else None,
                   "prow": [[int(a), int(b), int(rw)] for (a, b), rw in cg.prow.items()]}, open(out, "w"))


if __name__ == "__main__":
    main()
