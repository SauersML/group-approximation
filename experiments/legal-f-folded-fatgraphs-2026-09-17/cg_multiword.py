"""Column generation for the multiword polygon LP of balanced-power-boundaries-lift-to-folded-certificates.

System (the Corollary of that node): boundary B = Boundary(phi^m, W) for a finite word set W; variables
y_P >= 0 (vertex polygons, conventions of lp5.polygons) and n_w >= 0; rows
  dart d of the two circles of w:   sum_P y_P #{s : d_s = d} - n_w = 0
  pair {d, q}:                      sum_P y_P (#{s : (d_s,q_s) = (d,q)} - #{s : (d_s,q_s) = (q,d)}) = 0
  normalisation:                    sum_w n_w = 1
objective chi = sum_P y_P (1 - |P|/2).  A rational optimum < 0 gives a surface subgroup (Theorem +
positions construction of that node; realised explicitly by lift_word.py on the support columns).

The polygon set is never enumerated.  The master LP holds only generated columns; pair rows are created
when a column first uses the pair (an absent row has dual 0, which is a valid dual for the enlarged
master).  Pricing is exact: with duals (pi, mu) the reduced cost of P is
  base + sum_s cs(d_s, q_s),   cs(d, q) = cslot - pi_d - coef(d, q) mu_{dq},
a cycle d_1 -> ... -> d_k -> d_1 in the slot graph (d -> n allowed iff q = prv(n) is a legal partner of d).
Polygons have darts in pairwise distinct gates, so a k-gon is a sequence of k distinct gate blocks;
it is priced by min-plus products of the block cost matrices (k = 2, 3, 4; k <= maxval).  f-darts occur
only in 2-gons, at most one d^- dart per polygon.  Phase 1 minimises artificial infeasibility; phase 2
minimises chi.  When no column prices out, the master optimum is the optimum of the full LP.

usage: python3 cg_multiword.py '<phi0 json>' m out.json word [word ...] [--maxval K] [--kcol N] [--tl SEC]
"""
import sys, json, time, itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from ffold import Boundary, gate_of, inv, apply
from search3 import power

LET = "abcABC"
import os
SIMPLEX_STRATEGY = int(os.environ.get("CG_SIMPLEX", "1"))   # 1 = dual simplex (fastest in tests)
SOLVER = os.environ.get("CG_SOLVER", "simplex")


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


class CG:
    def __init__(self, phi, g, W, maxval):
        self.phi, self.W, self.maxval = phi, W, maxval
        B = Boundary(phi, W)
        self.B = B
        N = self.N = B.N
        gl = sorted({g[x] for x in LET})
        self.ngates = len(gl)
        self.gid = np.array([gl.index(g[B.label[d]]) for d in range(N)])
        self.mk = np.array([k == "-" for k in B.kind])
        self.fd = np.array(B.fdart, dtype=bool)
        self.prv = np.array(B.prv)
        self.nxt = np.array(B.nxt)
        li = np.array([LET.index(x) for x in B.label])
        invi = np.array([LET.index(inv(x)) for x in LET])
        ar = np.arange(N)
        Vq = (li[None, :] == invi[li][:, None])
        Vq &= ar[None, :] != self.prv[:, None]
        Vq &= ar[None, :] != self.nxt[:, None]
        Vq &= ~(self.mk[:, None] & self.mk[None, :])
        self.Vq = Vq                       # legal partner q of d
        self.E = Vq[:, self.prv]           # slot graph d -> n
        self.word = np.array([B.circle[d][0] for d in range(N)])
        self.ymax = max(np.sum(self.word == i) for i in range(len(W))) / 2.0
        self.cols = []
        self.colidx = []
        self.colset = set()
        # blocks for k >= 3: non-f darts by (gate, minus)
        self.blocks = {}
        for gi in range(self.ngates):
            for m in (False, True):
                idx = np.where((self.gid == gi) & (self.mk == m) & ~self.fd)[0]
                if len(idx):
                    self.blocks[(gi, m)] = idx

    def canon(self, darts):
        k = len(darts)
        i = min(range(k), key=lambda j: darts[j])
        ds = darts[i:] + darts[:i]
        return tuple((ds[s], int(self.prv[ds[(s + 1) % k]])) for s in range(k))

    def init_master(self):
        import highspy
        self.hs = highspy
        h = self.h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("threads", 1)
        if SOLVER == "ipm":                 # interior duals: better-centred prices, fewer CG rounds
            h.setOptionValue("solver", "ipm")
            h.setOptionValue("run_crossover", "off")
        else:
            h.setOptionValue("solver", "simplex")
            h.setOptionValue("simplex_strategy", SIMPLEX_STRATEGY)
        N, nW = self.N, len(self.W)
        self.inf = highspy.kHighsInf
        # rows 0..N-1 darts, row N normalisation, then pair rows
        h.addRows(N + 1, np.r_[np.zeros(N), 1.0], np.r_[np.zeros(N), 1.0], 0, np.zeros(N + 2, dtype=np.int32),
                  np.array([], dtype=np.int32), np.array([]))
        self.nrows = N + 1
        self.prow = {}
        self.ncols = 0
        self.art = []
        self.phase = 1
        # word columns
        for i in range(nW):
            ds = np.where(self.word == i)[0]
            idx = np.r_[ds, N].astype(np.int32)
            val = np.r_[-np.ones(len(ds)), 1.0]
            h.addCol(0.0, 0.0, self.inf, len(idx), idx, val)
        self.ncols = nW
        self._add_art(list(range(N)))

    def _add_art(self, rows):
        h = self.h
        for r0 in rows:
            for sg in (1.0, -1.0):
                h.addCol(1.0, 0.0, self.inf, 1, np.array([r0], dtype=np.int32), np.array([sg]))
                self.art.append(self.ncols); self.ncols += 1

    def add_cols(self, Ps):
        new = [P for P in Ps if P not in self.colset]
        newrows = []
        for P in new:
            self.colset.add(P)
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

    def solve_master(self, phase):
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

    def price(self, res, phase, kcol):
        N = self.N
        y = res.y
        pi = y[:N]
        MUs = np.zeros((N, N))
        if self.prow:
            ks = np.array(list(self.prow.keys())); rs = np.array(list(self.prow.values()))
            MUs[ks[:, 0], ks[:, 1]] = y[rs]
            MUs[ks[:, 1], ks[:, 0]] = -y[rs]
        base, cslot = (1.0, -0.5) if phase == 2 else (0.0, 0.0)
        Cq = cslot - pi[:, None] - MUs
        del MUs
        C = np.where(self.E, Cq[:, self.prv], np.inf)
        del Cq
        cand = []
        # 2-gons
        T = C + C.T + base
        ok = (self.gid[:, None] != self.gid[None, :]) & ~(self.mk[:, None] & self.mk[None, :]) \
            & ~(self.fd[:, None] & self.fd[None, :])
        ok &= np.triu(np.ones((N, N), dtype=bool), 1)
        T = np.where(ok, T, np.inf)
        del ok
        flat = T.ravel()
        k = min(kcol, int(np.sum(flat < -1e-9)))
        best2 = float(flat.min()) if flat.size else np.inf
        if k > 0:
            idx = np.argpartition(flat, k - 1)[:k]
            for t in idx:
                d1, d2 = divmod(int(t), N)
                cand.append((float(flat[t]), [d1, d2]))
        del T, flat
        bestk = {2: best2}
        # k-gons, k = 3, 4
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
                if kk == 3:
                    M12, a2 = minplus(C[np.ix_(I[0], I[1])], C[np.ix_(I[1], I[2])])
                    T = M12 + C[np.ix_(I[2], I[0])].T + base
                else:
                    M12, a2 = minplus(C[np.ix_(I[0], I[1])], C[np.ix_(I[1], I[2])])
                    M34, a4 = minplus(C[np.ix_(I[2], I[3])], C[np.ix_(I[3], I[0])])
                    T = M12 + M34.T + base
                flat = T.ravel()
                if flat.size == 0:
                    continue
                bk = min(bk, float(flat.min()))
                kn = min(kcol // 4 + 1, int(np.sum(flat < -1e-9)))
                if kn <= 0:
                    continue
                idx = np.argpartition(flat, kn - 1)[:kn]
                n3 = T.shape[1]
                for t in idx:
                    i1, i3 = divmod(int(t), n3)
                    d1, d3 = int(I[0][i1]), int(I[2][i3])
                    d2 = int(I[1][a2[i1, i3]])
                    if kk == 3:
                        cand.append((float(flat[t]), [d1, d2, d3]))
                    else:
                        d4 = int(I[3][a4[i3, i1]])
                        cand.append((float(flat[t]), [d1, d2, d3, d4]))
            bestk[kk] = bk
        cand.sort(key=lambda z: z[0])
        added = self.add_cols([self.canon(ds) for val, ds in cand[:kcol]])
        # word columns are always in the master; check them too
        return min(bestk.values()), added, bestk

    def run(self, kcol=3000, tl=1100, log=print):
        t0 = time.time()
        self.init_master()
        for phase in (1, 2):
            if phase == 2:
                self.to_phase2()
            it = 0
            while True:
                it += 1
                res = self.solve_master(phase)
                if res.status != 0:
                    log("master status", res.status, res.message)
                    return None, res
                rc, added, bestk = self.price(res, phase, kcol)
                # Lagrangian bound.  full opt z* = master opt + sum_j rc_j x*_j (duals of absent pair rows are 0).
                # Dart rows give sum_P y*_P |P| = sum_d n_w(d) (- a+_d + a-_d in phase 1) <= D + z* (phase 1),
                # D = max_w (|w| + |f(w)|), since sum n_w = 1 and every artificial costs 1 in phase 1.  |P| >= 2, so
                # z* >= master opt + min(0, rc) * (D + z*)/2 with z* <= master opt (phase 1), resp. D/2 (phase 2).
                ym = self.ymax + (res.fun / 2.0 if phase == 1 else 0.0)
                lb = res.fun + ym * min(0.0, rc)
                self.lb = max(getattr(self, "lb", -np.inf), lb) if phase == 2 else lb
                log("phase", phase, "it", it, "obj %.6f" % res.fun, "cols", len(self.cols), "pairs",
                    len(self.prow), "min rc %.4g" % rc, "LB %.4g" % lb, {k: round(v, 4) for k, v in bestk.items()},
                    "added", added, "t", round(time.time() - t0, 1), "tm", round(self.tmaster, 1), flush=True)
                if rc > -1e-9 or added == 0:
                    break
                if phase == 1 and lb > 1e-6:
                    log("phase 1 Lagrangian bound > 0: full LP infeasible")
                    return "infeasible", res
                if phase == 2 and lb > -1e-9:
                    log("phase 2 Lagrangian bound >= 0: full LP optimum >= 0")
                    return max(lb, 0.0), res
                if time.time() - t0 > tl:
                    log("time limit")
                    return "timeout", res
            if phase == 1 and res.fun > 1e-7:
                return "infeasible", res
        return res.fun, res


def necklaces(alph, L, lo=1):
    out = []
    for n in range(lo, L + 1):
        for t in itertools.product(alph, repeat=n):
            w = "".join(t)
            if any(w[i] == inv(w[(i + 1) % n]) for i in range(n)):
                continue
            rots = [w[i:] + w[:i] for i in range(n)]
            if w != min(rots) or any(w == w[:d] * (n // d) for d in range(1, n) if n % d == 0):
                continue
            out.append(w)
    return out


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--maxval", "--kcol", "--tl"):
        if key in args:
            i = args.index(key); opts[key] = int(args[i + 1]); del args[i:i + 2]
    neck = None
    if "--neck" in args:                  # --neck ALPH:L  all primitive necklaces over ALPH up to length L,
        i = args.index("--neck"); neck = args[i + 1]; del args[i:i + 2]   # plus their inverses
    phi0 = json.loads(args[0]); m = int(args[1]); out = args[2]; W = args[3:]
    if neck:
        from ffold import inv_word
        for part in neck.split(","):
            al, L = part.split(":")
            for w in necklaces(al, int(L)):
                for v in (w, inv_word(w)):
                    if v not in W:
                        W.append(v)
    phi = power(phi0, m)
    g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    maxval = opts.get("--maxval", max(2, 2 * min(gp, gn)))
    assert maxval <= 4, "pricing implemented for k <= 4"
    from ffold import cyc_legal
    W = [w for w in W if cyc_legal(g, w)]
    cg = CG(phi, g, W, maxval)
    print("phi0", phi0, "m", m, "words", len(W), "darts", cg.N, "maxval", maxval, "gates", cg.ngates, flush=True)
    val, res = cg.run(opts.get("--kcol", 3000), opts.get("--tl", 1100))
    print("RESULT", val, flush=True)
    if isinstance(val, float) and val < -1e-9:
        x = res.x
        sup = [j for j, jj in enumerate(cg.colidx) if x[jj] > 1e-9]
        nw = {W[i]: float(x[i]) for i in range(len(W)) if x[i] > 1e-9}
        print("support polygons", len(sup), "words", nw, flush=True)
        json.dump({"phi0": phi0, "power": m, "W": W, "chi": val, "n": nw,
                   "polygons": [[[int(d), int(q)] for d, q in cg.cols[j]] for j in sup],
                   "y": [float(x[cg.colidx[j]]) for j in sup],
                   "columns": [[[int(d), int(q)] for d, q in P] for P in cg.cols]}, open(out, "w"))


if __name__ == "__main__":
    main()
