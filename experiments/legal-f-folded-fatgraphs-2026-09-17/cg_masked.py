"""Column generation (cg_memory.CGM, IPM master) for the memory-r word-free LP restricted to a set of
boundary letters: windows outside the mask are fixed to 0, then exact support propagation (sp_mask) removes
every slot / window that is zero in all feasible points.  A feasible point of the restricted LP is feasible
for the full LP of lp_memory.py, so a negative restricted optimum proves the full optimum is negative;
restricted infeasibility / optimum >= 0 is a statement about boundaries over the mask only.
usage: python3 cg_masked.py '<phi0 json>' m r <letters, e.g. acAC> [--noprop | --live w1,w2,... | --propwin] [--kcol N] [--tl SEC] [--dual out.json]
"""
import sys, json, time, itertools
import numpy as np
import cg_memory as CG, lp_memory as LM, lp_allwords as LA, sp_mask as SP


class CGMask(CG.CGM):
    def restrict(self, S, walive):
        self.walive = np.array(walive, dtype=bool)
        tl = self.walive[np.array(self.TY.cw)]
        self.Vq = self.Vq & S & tl[:, None] & tl[None, :]
        # a dart of a dead type has no admissible slot, so no polygon passes through it: drop it from the blocks
        self.blocks = {k: idx[tl[idx]] for k, idx in self.blocks.items() if tl[idx].any()}

    def init_master(self):
        super().init_master()
        for j in range(self.nwin):
            if not self.walive[j]:
                self.h.changeColBounds(j, 0.0, 0.0)

    def window_rc(self, y):
        super().window_rc(np.zeros(self.rN + 1))
        v = -(self.WB.T @ y[:self.rN + 1])
        v = np.where(self.walive, v, np.inf)
        return float(min(0.0, v.min()))

    def dart_bound(self, y, phase, obj):
        # same as CGM.dart_bound, minimum over alive windows only
        yp = np.zeros(self.nrows); yp[:len(y)] = y; y = yp
        class Y: pass
        py = Y(); py.y = y
        base, C, _ = self.slot_costs(py, phase)
        ok2 = (self.gid[:, None] != self.gid[None, :]) & ~(self.mk[:, None] & self.mk[None, :]) \
            & ~(self.fd[:, None] & self.fd[None, :])
        T = np.where(ok2, C + C.T + base, np.inf)
        rho = np.minimum(0.0, T.min(axis=1) / 2.0)
        del T, ok2
        keys = list(self.blocks)
        for kk in (3, 4):
            for seq in itertools.permutations(keys, kk):
                gs = [s[0] for s in seq]
                if len(set(gs)) < kk or gs[0] != min(gs) or sum(s[1] for s in seq) > 1:
                    continue
                I = [self.blocks[s] for s in seq]
                Ms = [C[np.ix_(I[j], I[(j + 1) % kk])] for j in range(kk)]
                for j in range(kk):
                    P = Ms[j]
                    for t in range(1, kk):
                        P, _ = CG.minplus(P, Ms[(j + t) % kk])
                    rho[I[j]] = np.minimum(rho[I[j]], (np.diagonal(P) + base) / kk)
        wsum = np.zeros(self.nwin)
        np.add.at(wsum, np.array(self.TY.cw), rho)
        wsum = np.where(self.walive, wsum, np.inf)
        lb = float(y[self.rN]) + self.window_rc(y) + float(wsum.min())
        if phase == 1:
            lb += obj * float(rho.min())
            lb0 = lb - obj * float(rho.min())     # rho-shifted Farkas value (farkas_rho.py), no artificial term
            if lb0 > getattr(self, "best_rho", (-np.inf,))[0]:
                self.best_rho = (lb0, y.copy())
        return lb


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--kcol", "--tl"):
        if key in args:
            i = args.index(key); opts[key] = int(args[i + 1]); del args[i:i + 2]
    out = None
    if "--dual" in args:
        i = args.index("--dual"); out = args[i + 1]; del args[i:i + 2]
    phi0 = json.loads(args[0]); m = int(args[1]); r = int(args[2]); allowed = set(args[3])
    phi = LA.power(phi0, m); g = LA.gates(phi)
    TY = LM.MTypes(phi, g, r)
    mask = [set(v) <= allowed for v in TY.windows]
    live = None
    if "--live" in args:
        # windows left by an exact support propagation (sp_mask_sweep.py log): every feasible point of the masked
        # LP vanishes on the other windows, so a Farkas vector of the LP on these windows alone rules it out
        i = args.index("--live"); live = args[i + 1].split(","); del args[i:i + 2]
    if "--propwin" in args:
        # the same, with the surviving windows computed here (slots are not restricted beyond their windows)
        wp, _ = SP.propagate(TY, g, 4, log=lambda *a, **k: None, wmask=mask)
        live = ["".join(v) for j, v in enumerate(TY.windows) if wp[j]]
        print("propagation: surviving windows", live, flush=True)
        if not live:
            print("RESULT empty"); return
    if live is not None:
        walive = np.array([m and "".join(v) in live for m, v in zip(mask, TY.windows)], dtype=bool)
        assert int(walive.sum()) == len(set(live))
        tl = walive[np.array(TY.cw)]
        S = tl[:, None] & tl[None, :]
    elif "--noprop" in args:      # plain masked LP (dual is then a Farkas vector of the masked LP itself)
        walive = np.array(mask, dtype=bool)
        tl = walive[np.array(TY.cw)]
        S = tl[:, None] & tl[None, :]
    else:
        walive, S = SP.propagate(TY, g, 4, log=lambda *a, **k: None, wmask=mask)
    print("phi0", phi0, "m", m, "r", r, "mask", args[3], "windows alive", int(walive.sum()), "slots", int(S.sum()),
          flush=True)
    if not walive.any():
        print("RESULT empty"); return
    cg = CGMask(phi, g, TY, 4)
    cg.restrict(S, walive)
    val, res = cg.run(opts.get("--kcol", 3000), opts.get("--tl", 1100))
    print("RESULT", val, flush=True)
    if res is not None and hasattr(res, "x"):
        flow = {"".join(v): round(float(res.x[j]), 6) for j, v in enumerate(TY.windows) if res.x[j] > 1e-9}
        print("window flow", flow, flush=True)
    if out:
        json.dump({"phi0": phi0, "power": m, "r": r, "mask": args[3], "val": str(val), "live": live,
                   "columns": [[[int(d), int(q)] for d, q in P] for P in cg.cols],
                   "phase": cg.phase, "obj": float(res.fun) if res is not None else None,
                   "x": [float(v) for v in res.x] if res is not None else None,
                   "colidx": [int(j) for j in cg.colidx], "nwin": int(cg.nwin),
                   "rN": int(cg.rN), "y": [float(v) for v in res.y] if res is not None else None,
                   "rho_lb": float(cg.best_rho[0]) if hasattr(cg, "best_rho") else None,
                   "y_rho": [float(v) for v in cg.best_rho[1]] if hasattr(cg, "best_rho") else None,
                   "prow": [[int(a), int(b), int(rw)] for (a, b), rw in cg.prow.items()]}, open(out, "w"))


if __name__ == "__main__":
    main()
