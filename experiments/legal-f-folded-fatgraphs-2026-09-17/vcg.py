"""Column generation (cg_memory.CGM: IPM master, exact min-plus pricing, Lagrangian and dart-shift bounds) for the
mixed-memory LP of lp_vmem.py (d^- darts with memory rm, d^+ darts with memory rp, flow on (R+1)-windows).
The only changes from cg_memory.CGM are the row/column builder (lp_vmem.build) and the window sums of the dart
bound (a window counts every type in lp_vmem.VTypes.wt[window]).
usage: python3 vcg.py '<phi0 json>' m rm rp [--kcol N] [--tl SEC] [--dual out.json] [--load dump.json]
"""
import sys, json, time, itertools, os
import numpy as np
import cg_memory as CG
import lp_vmem as VM


class VCG(CG.CGM):
    def __init__(self, phi, g, TY, maxval):
        saved = CG.LM.build
        CG.LM.build = VM.build
        try:
            super().__init__(phi, g, TY, maxval)
        finally:
            CG.LM.build = saved
        self.wt = TY.wt

    def rho_of(self, y, phase):
        """rho_d = min(0, min over polygons P through d of rc_P / |P|), exact (min-plus)."""
        class Y: pass
        py = Y(); py.y = y
        base, C, _ = self.slot_costs(py, phase)
        ok2 = (self.gid[:, None] != self.gid[None, :]) & ~(self.mk[:, None] & self.mk[None, :]) \
            & ~(self.fd[:, None] & self.fd[None, :])
        T = np.where(ok2, C + C.T + base, np.inf)
        rho = np.minimum(0.0, T.min(axis=1) / 2.0)
        del T, ok2
        for kk in (3, 4):
            if kk > self.maxval:
                continue
            for seq in itertools.permutations(list(self.blocks), kk):
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
        return rho

    def dart_bound(self, y, phase, obj):
        yp = np.zeros(self.nrows); yp[:len(y)] = y; y = yp
        rho = self.rho_of(y, phase)
        wsum = np.array([rho[ts].sum() for ts in self.wt])
        lb = float(y[self.rN]) + self.window_rc(y) + float(wsum.min())
        if phase == 1:
            lb0 = lb                                # dart-shifted Farkas value (no artificial term)
            if lb0 > getattr(self, "best_rho", (-np.inf,))[0]:
                self.best_rho = (lb0, y.copy())
            lb += obj * float(rho.min())
            if lb0 > 1e-6:
                return lb0                          # a positive dart-shifted value already proves infeasibility
        return lb


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--kcol", "--tl"):
        if key in args:
            i = args.index(key); opts[key] = int(args[i + 1]); del args[i:i + 2]
    out = load = None
    if "--dual" in args:
        i = args.index("--dual"); out = args[i + 1]; del args[i:i + 2]
    if "--load" in args:
        i = args.index("--load"); load = args[i + 1]; del args[i:i + 2]
    phi0 = json.loads(args[0]); m, rm, rp = int(args[1]), args[2], args[3]
    phi, g, TY, maxval = VM.setup(phi0, m, rm, rp)
    assert maxval <= 4
    cg = VCG(phi, g, TY, maxval)
    print("phi0", phi0, "m", m, "rm", rm, "rp", rp, "windows", len(TY.windows), "types", cg.N, "maxval", maxval,
          flush=True)
    init = None
    if load:
        init = [tuple(tuple(sl) for sl in P) for P in json.load(open(load))["columns"]]
    val, res = cg.run(opts.get("--kcol", 3000), opts.get("--tl", 1100), init=init)
    print("RESULT", val, flush=True)
    if hasattr(cg, "best_rho"):
        print("best dart-shifted phase-1 value", cg.best_rho[0], flush=True)
    if res is not None and hasattr(res, "x"):
        flow = {"".join(v): round(float(res.x[j]), 6) for j, v in enumerate(TY.windows) if res.x[j] > 1e-9}
        print("window flow", flow, flush=True)
    if out:
        J = {"phi0": phi0, "power": m, "rm": rm, "rp": rp, "val": str(val), "phase": cg.phase,
             "columns": [[[int(d), int(q)] for d, q in P] for P in cg.cols],
             "obj": float(res.fun) if res is not None else None, "rN": int(cg.rN),
             "y": [float(v) for v in res.y] if res is not None else None,
             "prow": [[int(a), int(b), int(rw)] for (a, b), rw in cg.prow.items()]}
        if hasattr(cg, "best_rho"):
            J["rho_lb"] = float(cg.best_rho[0]); J["y_rho"] = [float(v) for v in cg.best_rho[1]]
        if res is not None:
            J["x"] = [float(v) for v in res.x]; J["colidx"] = [int(j) for j in cg.colidx]
        json.dump(J, open(out, "w"))


if __name__ == "__main__":
    main()
