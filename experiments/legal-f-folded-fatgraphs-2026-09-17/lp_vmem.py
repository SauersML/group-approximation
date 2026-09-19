"""Mixed-memory word-free certificate LP: d^- darts and d^+ darts remember different amounts of the word.

Conventions as in lp_memory.py.  Fix R = max(rm, rp).  Flow variables c_w live on the windows w of R + 1
letters (de Bruijn circulation on R-paths, zero homology, sum c = 1), exactly as in lp_memory.py with r = R.
Dart types are coarser:
  ('-', v)      v = (x_j, ..., x_{j+rm})            count = sum of c_w over windows w with w[:rm+1] = v
  ('+', v, i)   v = (x_{j-rp}, ..., x_j), dart i of R(x_j)   count = sum of c_w over w with w[R-rp:] = v
Successors as in lp_memory.MTypes with r = rm (for d^-) and r = rp (for d^+); a memory-0 dart forgets
everything but its letter, and its successors are all legal continuations.

Projection.  A legal f^m-folded fatgraph X gives the point of lp_memory.py (memory R): c_w = occurrences of w,
y_P = number of vertices of X of typed polygon P.  Forgetting part of each dart's window maps every typed
polygon of memory R to a typed polygon here (the successor of a dart in X is a successor of its coarse type, the
gate, minus and f-dart conditions depend on labels only), keeps the pair balance (it sums pair rows), and the
type counts become the stated sums of c.  So the point projects to a feasible point with the same chi, and
min chi >= 0 (or infeasibility) here rules out every certificate.  `validate` checks this on certificates.
This LP is a relaxation of lp_memory.py with r = R, and refines lp_memory.py with r = min(rm, rp).

usage: python3 lp_vmem.py '<phi0 json>' m rm rp          (enumerate polygons, solve directly)
       python3 lp_vmem.py --validate rm rp cert.json [...]
"""
import sys, json, time
from fractions import Fraction
from collections import Counter
import numpy as np
from ffold import inv, inv_word
import lp_allwords as LA
import lp_memory as LM


class VTypes:
    """rm, rp: an int (uniform memory) or a dict letter -> memory.  A d^- dart reading x_j remembers
    x_j..x_{j+rm(x_j)}; a d^+ dart of the block R(x_j) remembers x_{j-rp(x_j)}..x_j."""
    def __init__(self, phi, g, rm, rp):
        letters = sorted(phi)
        self.L = letters + [x.upper() for x in letters]
        if isinstance(rm, int): rm = {x: rm for x in self.L}
        if isinstance(rp, int): rp = {x: rp for x in self.L}
        self.phi, self.rmf, self.rpf = phi, rm, rp
        self.rm = max(rm.values()); self.rp = max(rp.values())
        self.r = R = max(self.rm, self.rp)
        self.R = {x: inv_word(phi[x] if x.islower() else inv_word(phi[x.lower()])) for x in self.L}
        legal = {(x, y) for x in self.L for y in self.L if y != inv(x) and g[inv(x)] != g[y]}
        self.legal = legal

        def paths(k):
            W = [(x,) for x in self.L]
            for _ in range(k):
                W = [v + (z,) for v in W for z in self.L if (v[-1], z) in legal]
            return W
        self.windows = paths(R)
        self.widx = {v: i for i, v in enumerate(self.windows)}
        allp = [p for k in range(R + 1) for p in paths(k)]
        Cm = [v for v in allp if len(v) == rm[v[0]] + 1]
        Cp = [v for v in allp if len(v) == rp[v[-1]] + 1]
        T = [("-", v) for v in Cm]
        for v in Cp:
            for i in range(len(self.R[v[-1]])):
                T.append(("+", v, i))
        self.T = T
        self.idx = {t: i for i, t in enumerate(T)}
        self.label, self.fdart, self.kind = [], [], []
        for t in T:
            if t[0] == "-":
                self.label.append(t[1][0]); self.fdart.append(False); self.kind.append("-")
            else:
                self.label.append(self.R[t[1][-1]][t[2]]); self.fdart.append(t[2] == 0); self.kind.append("+")
        cm = {v: [] for v in Cm}; cp = {v: [] for v in Cp}
        for j, w in enumerate(self.windows):
            cm[w[:rm[w[0]] + 1]].append(j); cp[w[R - rp[w[-1]]:]].append(j)
        self.tw = [cm[t[1]] if t[0] == "-" else cp[t[1]] for t in T]
        # successors: every coarse context consistent with what the dart remembers
        self.succ = []
        for t in T:
            v = t[1]
            if t[0] == "-":
                known = v[1:]
                s = [self.idx[("-", u)] for u in Cm
                     if (v[0], u[0]) in legal and u[:len(known)] == known[:len(u)]]
            elif t[2] + 1 < len(self.R[v[-1]]):
                s = [self.idx[("+", v, t[2] + 1)]]
            else:
                known = v[:-1]
                s = [self.idx[("+", u, 0)] for u in Cp
                     if (u[-1], v[-1]) in legal and (len(known) == 0 or u[-min(len(u), len(known)):] ==
                                                    known[len(known) - min(len(u), len(known)):])]
            self.succ.append(s)
        self.N = len(T)
        self.bylabel = {x: [i for i in range(self.N) if self.label[i] == x] for x in self.L}
        self.wt = [[] for _ in self.windows]
        for i, ws in enumerate(self.tw):
            for j in ws:
                self.wt[j].append(i)

    def dart_type(self, w, j, kind, i=0):
        """type of the dart at position j of cyclic word w (kind '-': the d^- dart reading w[j];
        kind '+': dart i of the block R(w[j]))."""
        L = len(w)
        if kind == "-":
            return self.idx[("-", tuple(w[(j + s) % L] for s in range(self.rmf[w[j]] + 1)))]
        k = self.rpf[w[j]]
        return self.idx[("+", tuple(w[(j - k + s) % L] for s in range(k + 1)), i)]


def build(TY, polys):
    """rows: types, pairs (created by polygons), R-path circulation, homology; columns: polygons, windows."""
    N = TY.N
    pairs = {}
    cols = []
    for P in polys:
        col = {}
        for (d, q) in P:
            col[d] = col.get(d, 0) + 1
            key = (min(d, q), max(d, q))
            rr = pairs.setdefault(key, N + len(pairs))
            col[rr] = col.get(rr, 0) + (1 if d < q else -1)
        cols.append(col)
    r0 = N + len(pairs)
    W = TY.windows
    ccols = [dict() for _ in W]
    for j in range(len(W)):
        for i in TY.wt[j]:
            ccols[j][i] = ccols[j].get(i, 0) - 1
    prefixes = sorted({v[:-1] for v in W} | {v[1:] for v in W})
    pidx = {s: r0 + k for k, s in enumerate(prefixes)}
    letters = sorted(TY.phi)
    hom = {x: r0 + len(prefixes) + k for k, x in enumerate(letters)}
    for j, v in enumerate(W):
        a, b = pidx[v[:-1]], pidx[v[1:]]
        ccols[j][a] = ccols[j].get(a, 0) + 1
        ccols[j][b] = ccols[j].get(b, 0) - 1
        x = v[0]
        ccols[j][hom[x.lower()]] = ccols[j].get(hom[x.lower()], 0) + (1 if x.islower() else -1)
    nrows = r0 + len(prefixes) + len(letters)
    return nrows, cols, ccols


def parse_mem(s):
    """'2' -> 2 (uniform); 'a2b1c2' -> {a: 2, A: 2, b: 1, B: 1, c: 2, C: 2} (x and x^-1 share a memory)."""
    if isinstance(s, int) or s.isdigit():
        return int(s)
    d = {}
    for k in range(0, len(s), 2):
        d[s[k].lower()] = d[s[k].upper()] = int(s[k + 1])
    return d


def setup(phi0, m, rm, rp, maxval=None):
    rm, rp = parse_mem(rm), parse_mem(rp)
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    if maxval is None:
        maxval = max(2, 2 * min(gp, gn))
    TY = VTypes(phi, g, rm, rp)
    return phi, g, TY, maxval


def validate(rm, rp, paths):
    """project actual certificates: every vertex is an enumerated typed polygon, all rows balance."""
    bad = 0
    for path in paths:
        cert = json.load(open(path))
        phi, g, TY, maxval = setup(cert["phi0"], cert["power"], rm, rp)
        polys = LM.polygons(TY, g, maxval)
        pidx = {P: j for j, P in enumerate(polys)}
        label, tm, nxt = [], [], []
        cnt = Counter()
        R = TY.r
        for w in cert["minus_words"]:
            L = len(w); start = len(label)
            for i in range(L):
                label.append(w[i]); tm.append(TY.dart_type(w, i, "-"))
                cnt[tuple(w[(i + s) % L] for s in range(R + 1))] += 1
            nxt.extend(start + (i + 1) % L for i in range(L))
            start = len(label)
            for t in range(L - 1, -1, -1):
                blk = TY.R[w[t]]
                for i in range(len(blk)):
                    label.append(blk[i]); tm.append(TY.dart_type(w, t, "+", i))
            n = len(label) - start
            nxt.extend(start + (i + 1) % n for i in range(n))
        p = cert["pairing"]; N = len(label)
        assert len(p) == N
        for d in range(N):
            assert TY.label[tm[d]] == label[d]
            assert tm[nxt[d]] in TY.succ[tm[d]], ("successor", d)
            assert p[p[d]] == d and label[p[d]] == inv(label[d])
        seen, y = set(), Counter()
        ok = True
        for d0 in range(N):
            if d0 in seen:
                continue
            orb, d = [], d0
            while d not in seen:
                seen.add(d); orb.append(d); d = nxt[p[d]]
            sl = [(tm[x], tm[p[x]]) for x in orb]
            k = min(range(len(sl)), key=lambda i: sl[i][0])
            sl = tuple(sl[k:] + sl[:k])
            if sl not in pidx:
                print(path, "vertex polygon not enumerated", sl[:3], len(sl)); bad += 1; ok = False
                break
            y[pidx[sl]] += 1
        if not ok:
            continue
        nrows, cols, ccols = build(TY, polys)
        tot = Counter()
        for j, n in y.items():
            for row, val in cols[j].items():
                tot[row] += n * val
        for v, n in cnt.items():
            for row, val in ccols[TY.widx[v]].items():
                tot[row] += n * val
        nz = {row: val for row, val in tot.items() if val != 0}
        chi = sum(n * Fraction(2 - len(polys[j]), 2) for j, n in y.items())
        print(path, "rm", rm, "rp", rp, "types", TY.N, "polygons", len(polys), "darts", N, "vertices",
              sum(y.values()), "chi", chi, "nonzero rows", len(nz), flush=True)
        bad += bool(nz)
    print("failures", bad)
    return bad


def main(phi0, m, rm, rp):
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    t0 = time.time()
    phi, g, TY, maxval = setup(phi0, m, rm, rp)
    polys = LM.polygons(TY, g, maxval)
    print("phi0", phi0, "m", m, "rm", rm, "rp", rp, "windows", len(TY.windows), "types", TY.N, "polygons",
          len(polys), "t", round(time.time() - t0, 1), flush=True)
    nrows, cols, ccols = build(TY, polys)
    ny, nc = len(cols), len(ccols)
    r, c, v = [], [], []
    for j, col in enumerate(cols):
        for row, val in col.items():
            r.append(row); c.append(j); v.append(float(val))
    for j, col in enumerate(ccols):
        for row, val in col.items():
            r.append(row); c.append(ny + j); v.append(float(val))
        r.append(nrows); c.append(ny + j); v.append(1.0)
    A = coo_matrix((v, (r, c)), shape=(nrows + 1, ny + nc)).tocsr()
    b = np.zeros(nrows + 1); b[nrows] = 1.0
    cost = np.array([1.0 - len(P) / 2.0 for P in polys] + [0.0] * nc)
    res = linprog(cost, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    print("lp status", res.status, res.message, "min chi", res.fun, "t", round(time.time() - t0, 1), flush=True)
    if res.status == 0:
        x = res.x
        cv = {"".join(TY.windows[j]): round(x[ny + j], 5) for j in range(nc) if x[ny + j] > 1e-9}
        print("window flow", cv, flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "--validate":
        sys.exit(validate(sys.argv[2], sys.argv[3], sys.argv[4:]))
    main(json.loads(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4])
