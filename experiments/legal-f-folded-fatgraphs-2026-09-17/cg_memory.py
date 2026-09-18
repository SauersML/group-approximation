"""Column generation for the memory-r word-free polygon LP of lp_memory.py (all boundaries at once).

lp_memory.py enumerates every typed vertex polygon, which stops at r = 1 (446704 polygons for entry 4887 at
power 2).  Here the master LP holds only generated polygon columns plus all window-circulation columns;
pair rows are created when a column first uses the pair (an absent row has dual 0).  Rows and columns are
those of lp_memory.build:
  type tau:        sum_P y_P #{s : d_s = tau} - c_{window(tau)} = 0
  pair {tau, s}:   sum_P y_P (#slots tau->s - #slots s->tau) = 0
  r-path u:        sum_{v : v[:-1] = u} c_v - sum_{v : v[1:] = u} c_v = 0
  homology x:      sum_v c_v [v_0 = x^{+-1}] = 0,     normalisation sum_v c_v = 1
objective chi = sum_P y_P (1 - |P|/2).  Every legal f^m-folded fatgraph with chi < 0 projects to a feasible
point with chi < 0 (lp_memory.validate), so an optimum >= 0 (or infeasibility) rules out all of them.

Pricing is exact.  Slot (d -> q) followed by dart n needs label(q) = label(d)^{-1}, not both d^-, and n in
succ(q); its cost is cs(d, q) = cslot - pi_d - coef mu_{dq}, and C[d, n] = min_q cs(d, q).  A k-gon is a
cycle of k darts in pairwise distinct gates (at most one d^-, an f-dart only in a 2-gon), priced by min-plus
products over (gate, minus) blocks, k <= 4.

Lagrangian bound: the full optimum z* = master optimum + sum_P rc_P y*_P.  In phase 2, sum_P y_P |P| = sum
of type counts = sum_v c_v (1 + |R(v_last)|) <= 1 + max_x |f(x)|, so sum_P y_P <= Ymax = (1 + max|f(x)|)/2
and z* >= master + Ymax min(0, rc); in phase 1 add the artificial mass (<= master objective) to Ymax.

usage: python3 cg_memory.py '<phi0 json>' m r [--kcol N] [--tl SEC] [--dual out.json]
"""
import sys, json, time, itertools, os
import numpy as np
import lp_memory as LM
import lp_allwords as LA
from ffold import inv

SOLVER = os.environ.get("CG_SOLVER", "ipm")


def minplus(A, Bm):
    n1, n2 = A.shape
    n3 = Bm.shape[1]
    out = np.full((n1, n3), np.inf)
    arg = np.zeros((n1, n3), dtype=np.int64)
    if n1 == 0 or n2 == 0 or n3 == 0:
        return out, arg
    ch = max(1, int(3e6 // max(1, n1 * n3)))
    for k0 in range(0, n2, ch):
        S = A[:, k0:k0 + ch, None] + Bm[None, k0:k0 + ch, :]
        a = S.argmin(axis=1)
        v = np.take_along_axis(S, a[:, None, :], axis=1)[:, 0, :]
        better = v < out
        out[better] = v[better]
        arg[better] = a[better] + k0
    return out, arg


class CGM:
    def __init__(self, phi, g, TY, maxval):
        self.TY, self.maxval = TY, maxval
        N = self.N = TY.N
        LET = TY.L
        gl = sorted({g[x] for x in LET})
        self.ngates = len(gl)
        self.gid = np.array([gl.index(g[TY.label[d]]) for d in range(N)])
        self.mk = np.array([k == "-" for k in TY.kind])
        self.fd = np.array(TY.fdart, dtype=bool)
        li = np.array([LET.index(x) for x in TY.label])
        invi = np.array([LET.index(inv(x)) for x in LET])
        Vq = (li[None, :] == invi[li][:, None])
        Vq &= ~(self.mk[:, None] & self.mk[None, :])
        self.Vq = Vq
        # successor edges q -> n
        self.eq = np.array([q for q in range(N) for n in TY.succ[q]])
        self.en = np.array([n for q in range(N) for n in TY.succ[q]])
        self.blocks = {}
        for gi in range(self.ngates):
            for m in (False, True):
                idx = np.where((self.gid == gi) & (self.mk == m) & ~self.fd)[0]
                if len(idx):
                    self.blocks[(gi, m)] = idx
        self.nrows_built = LM.build(TY, [])        # rows of the window columns (no polygons yet)
        self.cols, self.colidx, self.colset = [], [], set()
        self.ymax = (1 + max(len(TY.R[x]) for x in LET)) / 2.0

    def init_master(self):
        import highspy
        self.hs = highspy
        h = self.h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("threads", 1)
        if SOLVER == "ipm":
            h.setOptionValue("solver", "ipm")
            h.setOptionValue("run_crossover", "off")
        else:
            h.setOptionValue("solver", "simplex")
            h.setOptionValue("simplex_strategy", 1)
        self.inf = highspy.kHighsInf
        N = self.N
        # row layout: 0..N-1 types, then circulation/homology rows, then normalisation, then pair rows
        nrows0, _, ccols = self.nrows_built       # nrows0 = N + 0 pairs + prefixes + letters
        self.rN = nrows0
        lo = np.zeros(nrows0 + 1); lo[nrows0] = 1.0
        h.addRows(nrows0 + 1, lo, lo.copy(), 0, np.zeros(nrows0 + 2, dtype=np.int32),
                  np.array([], dtype=np.int32), np.array([]))
        self.nrows = nrows0 + 1
        self.prow = {}
        self.ncols = 0
        self.art = []
        self.phase = 1
        for col in ccols:
            idx = np.array(list(col) + [nrows0], dtype=np.int32)
            val = np.array([float(col[i]) for i in col] + [1.0])
            h.addCol(0.0, 0.0, self.inf, len(idx), idx, val)
            self.ncols += 1
        self.nwin = len(ccols)
        self._add_art(list(range(nrows0)))

    def _add_art(self, rows):
        for r0 in rows:
            for sg in (1.0, -1.0):
                self.h.addCol(1.0, 0.0, self.inf, 1, np.array([r0], dtype=np.int32), np.array([sg]))
                self.art.append(self.ncols); self.ncols += 1

    def add_cols(self, Ps):
        new = []
        for P in Ps:
            if P not in self.colset:
                self.colset.add(P); new.append(P)
        newrows = []
        for P in new:
            for (d, q) in P:
                key = (min(d, q), max(d, q))
                if key not in self.prow:
                    self.prow[key] = self.nrows; self.nrows += 1; newrows.append(self.prow[key])
        if newrows:
            k = len(newrows)
            self.h.addRows(k, np.zeros(k), np.zeros(k), 0, np.zeros(k + 1, dtype=np.int32),
                           np.array([], dtype=np.int32), np.array([]))
            if self.phase == 1:
                self._add_art(newrows)
        for P in new:
            col = {}
            for (d, q) in P:
                col[d] = col.get(d, 0) + 1.0
                r = self.prow[(min(d, q), max(d, q))]
                col[r] = col.get(r, 0) + (1.0 if d < q else -1.0)
            idx = np.array(list(col), dtype=np.int32); val = np.array([col[i] for i in col])
            cost = (1.0 - len(P) / 2.0) if self.phase == 2 else 0.0
            self.h.addCol(cost, 0.0, self.inf, len(idx), idx, val)
            self.cols.append(P); self.colidx.append(self.ncols); self.ncols += 1
        return len(new)

    def to_phase2(self):
        self.phase = 2
        for j in self.art:
            self.h.changeColBounds(j, 0.0, 0.0)
            self.h.changeColCost(j, 0.0)
        for P, j in zip(self.cols, self.colidx):
            self.h.changeColCost(j, 1.0 - len(P) / 2.0)

    def solve_master(self):
        t = time.time()
        self.h.run()
        self.tmaster = getattr(self, "tmaster", 0.0) + time.time() - t
        st = self.h.getModelStatus()
        s = self.h.getSolution()
        class R: pass
        res = R()
        res.status = 0 if st == self.hs.HighsModelStatus.kOptimal else 1
        res.message = str(st)
        res.fun = self.h.getInfo().objective_function_value
        res.y = np.array(s.row_dual)
        res.x = np.array(s.col_value)
        return res

    def slot_costs(self, res, phase):
        N = self.N
        y = res.y
        pi = y[:N]
        MUs = np.zeros((N, N))
        if self.prow:
            ks = np.array(list(self.prow.keys())); rs = np.array(list(self.prow.values()))
            MUs[ks[:, 0], ks[:, 1]] = y[rs]
            MUs[ks[:, 1], ks[:, 0]] = -y[rs]
        base, cslot = (1.0, -0.5) if phase == 2 else (0.0, 0.0)
        Cq = np.where(self.Vq, cslot - pi[:, None] - MUs, np.inf)
        del MUs
        C = np.full((N, N), np.inf)
        Q = np.full((N, N), -1, dtype=np.int64)
        for q, n in zip(self.eq, self.en):
            col = Cq[:, q]
            better = col < C[:, n]
            C[better, n] = col[better]
            Q[better, n] = q
        return base, C, Q

    def price(self, res, phase, kcol):
        N = self.N
        base, C, Q = self.slot_costs(res, phase)
        cand = []
        T = C + C.T + base
        ok = (self.gid[:, None] != self.gid[None, :]) & ~(self.mk[:, None] & self.mk[None, :]) \
            & ~(self.fd[:, None] & self.fd[None, :])
        ok &= np.triu(np.ones((N, N), dtype=bool), 1)
        T = np.where(ok, T, np.inf)
        del ok
        flat = T.ravel()
        best2 = float(flat.min())
        k = min(kcol, int(np.sum(flat < -1e-9)))
        if k > 0:
            for t in np.argpartition(flat, k - 1)[:k]:
                d1, d2 = divmod(int(t), N)
                cand.append((float(flat[t]), [d1, d2]))
        del T, flat
        bestk = {2: best2}
        keys = list(self.blocks)
        for kk in (3, 4):
            if kk > self.maxval:
                continue
            bk = np.inf
            for seq in itertools.permutations(keys, kk):
                gs = [s[0] for s in seq]
                if len(set(gs)) < kk or gs[0] != min(gs) or sum(s[1] for s in seq) > 1:
                    continue
                I = [self.blocks[s] for s in seq]
                M12, a2 = minplus(C[np.ix_(I[0], I[1])], C[np.ix_(I[1], I[2])])
                if kk == 3:
                    T = M12 + C[np.ix_(I[2], I[0])].T + base
                else:
                    M34, a4 = minplus(C[np.ix_(I[2], I[3])], C[np.ix_(I[3], I[0])])
                    T = M12 + M34.T + base
                flat = T.ravel()
                if flat.size == 0:
                    continue
                bk = min(bk, float(flat.min()))
                kn = min(kcol // 4 + 1, int(np.sum(flat < -1e-9)))
                if kn <= 0:
                    continue
                n3 = T.shape[1]
                for t in np.argpartition(flat, kn - 1)[:kn]:
                    i1, i3 = divmod(int(t), n3)
                    d1, d3 = int(I[0][i1]), int(I[2][i3])
                    d2 = int(I[1][a2[i1, i3]])
                    ds = [d1, d2, d3] if kk == 3 else [d1, d2, d3, int(I[3][a4[i3, i1]])]
                    cand.append((float(flat[t]), ds))
            bestk[kk] = bk
        cand.sort(key=lambda z: z[0])
        Ps = []
        for val, ds in cand[:kcol]:
            k = len(ds)
            sl = [(ds[s], int(Q[ds[s], ds[(s + 1) % k]])) for s in range(k)]
            i = min(range(k), key=lambda j: sl[j][0])
            Ps.append(tuple(sl[i:] + sl[:i]))
        added = self.add_cols(Ps)
        return min(bestk.values()), added, bestk

    def window_rc(self, y):
        """min over window columns of -pi . B_c (their cost is 0 in both phases)."""
        if not hasattr(self, "WB"):
            from scipy.sparse import coo_matrix
            r, c, v = [], [], []
            for j, col in enumerate(self.nrows_built[2]):
                for row, val in col.items():
                    r.append(row); c.append(j); v.append(float(val))
                r.append(self.rN); c.append(j); v.append(1.0)
            self.WB = coo_matrix((v, (r, c)), shape=(self.rN + 1, self.nwin)).tocsc()
        return float(min(0.0, (-(self.WB.T @ y[:self.rN + 1])).min()))

    def bound(self, y, rcP, phase, obj):
        """Lagrangian lower bound on the full phase-`phase` optimum at an arbitrary dual vector y with
        |y_row| <= 1 on rows carrying artificials (true for master duals and their convex combinations)."""
        ym = self.ymax + (obj / 2.0 if phase == 1 else 0.0)
        return float(y[self.rN]) + self.window_rc(y) + ym * min(0.0, rcP)

    def dart_bound(self, y, phase, obj):
        """Dart-wise Lagrangian bound.  rho_d = min(0, min_{P containing d} rc_P / |P|), so rc_P >= sum_{d in P} rho_d
        (the darts of P are distinct) and sum_P y_P rc_P >= sum_d rho_d n_d, n_d the count of type d.  In phase 2
        n_d = c_{window(d)}; in phase 1 n_d <= c_{window(d)} + art_d^- and the artificial mass is <= obj.  With
        sum_v c_v = 1:  z* >= y_norm + min(0, min window rc) + min_v sum_{d in v} rho_d (+ obj min_d rho_d)."""
        class Y: pass
        yp = np.zeros(self.nrows); yp[:len(y)] = y      # rows added after this solve carry dual 0
        y = yp
        py = Y(); py.y = y
        base, C, _ = self.slot_costs(py, phase)
        N = self.N
        ok2 = (self.gid[:, None] != self.gid[None, :]) & ~(self.mk[:, None] & self.mk[None, :]) \
            & ~(self.fd[:, None] & self.fd[None, :])
        T = np.where(ok2, C + C.T + base, np.inf)
        rho = np.minimum(0.0, T.min(axis=1) / 2.0)
        del T, ok2
        keys = list(self.blocks)
        for kk in (3, 4):
            if kk > self.maxval:
                continue
            for seq in itertools.permutations(keys, kk):
                gs = [s[0] for s in seq]
                if len(set(gs)) < kk or gs[0] != min(gs) or sum(s[1] for s in seq) > 1:
                    continue
                I = [self.blocks[s] for s in seq]
                Ms = [C[np.ix_(I[j], I[(j + 1) % kk])] for j in range(kk)]
                for j in range(kk):
                    P = Ms[j]
                    for t in range(1, kk):
                        P, _ = minplus(P, Ms[(j + t) % kk])
                    dg = np.diagonal(P) + base
                    rho[I[j]] = np.minimum(rho[I[j]], dg / kk)
        cw = np.array(self.TY.cw)
        wsum = np.zeros(self.nwin)
        np.add.at(wsum, cw, rho)
        lb = float(y[self.rN]) + self.window_rc(y) + float(wsum.min())
        if phase == 1:
            lb += obj * float(rho.min())
        return lb

    def run(self, kcol=3000, tl=1100, log=print, init=None, alpha=None):
        if alpha is None:
            alpha = float(os.environ.get("CG_ALPHA", "0.0"))
        t0 = time.time()
        self.init_master()
        if init:
            self.add_cols([tuple(tuple(sl) for sl in P) for P in init])
        class Y: pass
        for phase in (1, 2):
            if phase == 2:
                self.to_phase2()
            it = 0
            center, best = None, -np.inf
            while True:
                it += 1
                res = self.solve_master()
                if res.status != 0:
                    log("master status", res.status, res.message)
                    return None, res
                y = res.y
                if center is not None and alpha > 0:
                    cp = np.zeros(len(y)); cp[:len(center)] = center
                    ys = alpha * cp + (1 - alpha) * y
                else:
                    ys = y
                py = Y(); py.y = ys
                rc, added, bestk = self.price(py, phase, kcol)
                lb = self.bound(ys, rc, phase, res.fun)
                mis = ""
                if lb > best:
                    best, center = lb, ys.copy()
                if added == 0 and ys is not y:
                    mis = " misprice"
                    rc, added, bestk = self.price(res, phase, kcol)
                    lb = self.bound(y, rc, phase, res.fun)
                    if lb > best:
                        best, center = lb, y.copy()
                rev = int(os.environ.get("CG_RHO_EVERY", "5"))
                if rev > 0 and it % rev == 0:
                    lbd = self.dart_bound(y, phase, res.fun)
                    mis += " dartLB %.4g" % lbd
                    if lbd > best:
                        best = lbd
                log("phase", phase, "it", it, "obj %.6f" % res.fun, "cols", len(self.cols), "pairs",
                    len(self.prow), "min rc %.4g" % rc, "LB %.4g" % lb, "best %.4g" % best,
                    {k: round(v, 4) for k, v in bestk.items()}, "added", added,
                    "t", round(time.time() - t0, 1), "tm", round(self.tmaster, 1) + 0, mis, flush=True)
                if added == 0 or (phase == 1 and res.fun < 1e-9):
                    break
                if phase == 2 and os.environ.get("CG_SIGN") and res.fun < -1e-7:
                    log("phase 2 master already negative: the full LP optimum is < 0")
                    return ("negative", res.fun), res
                if phase == 1 and best > 1e-6:
                    log("phase 1 Lagrangian bound > 0: full LP infeasible")
                    return "infeasible", res
                if phase == 2 and best > -1e-9:
                    log("phase 2 Lagrangian bound >= 0: full LP optimum >= 0")
                    return max(best, 0.0), res
                if time.time() - t0 > tl:
                    log("time limit")
                    return ("timeout", best), res
            if phase == 1 and res.fun > 1e-7:
                return "infeasible", res
        return res.fun, res


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--kcol", "--tl", "--maxval"):
        if key in args:
            i = args.index(key); opts[key] = int(args[i + 1]); del args[i:i + 2]
    out = None
    init = None
    if "--load" in args:
        i = args.index("--load"); init = json.load(open(args[i + 1]))["columns"]; del args[i:i + 2]
    if "--dual" in args:
        i = args.index("--dual"); out = args[i + 1]; del args[i:i + 2]
    phi0 = json.loads(args[0]); m = int(args[1]); r = int(args[2])
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    maxval = opts.get("--maxval", max(2, 2 * min(gp, gn)))
    assert maxval <= 4
    TY = LM.MTypes(phi, g, r)
    cg = CGM(phi, g, TY, maxval)
    print("phi0", phi0, "m", m, "r", r, "windows", len(TY.windows), "types", cg.N, "maxval", maxval, flush=True)
    val, res = cg.run(opts.get("--kcol", 3000), opts.get("--tl", 1100), init=init)
    print("RESULT", val, flush=True)
    if res is not None and hasattr(res, "x"):
        flow = {"".join(v): float(res.x[j]) for j, v in enumerate(TY.windows) if res.x[j] > 1e-9}
        print("window flow", flow, flush=True)
    if out:
        json.dump({"phi0": phi0, "power": m, "r": r, "val": str(val),
                   "columns": [[[int(d), int(q)] for d, q in P] for P in cg.cols],
                   "phase": cg.phase, "obj": float(res.fun) if res is not None else None,
                   "rN": int(cg.rN), "y": [float(v) for v in res.y] if res is not None else None,
                   "prow": [[int(a), int(b), int(rw)] for (a, b), rw in cg.prow.items()]}, open(out, "w"))


if __name__ == "__main__":
    main()
