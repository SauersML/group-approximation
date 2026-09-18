"""Word-free certificate LP with memory r: every boundary dart remembers a window of r+1 letters of w.

Conventions as in lp_allwords.py (legal f-folded fatgraph X, d^- = legal cyclic words w, d^+ circle of
w = f(x_L)^{-1} ... f(x_1)^{-1} for w = x_1 ... x_L, block R(x) = f(x)^{-1}, f-dart = first dart of a
block).  A window is a legal path v = (v_0, ..., v_r) of r+1 letters (all r turns legal).
TYPES
  ('-', v)      a d^- dart reading x_j, where v = (x_j, x_{j+1}, ..., x_{j+r})   (future letters)
  ('+', v, i)   dart i of the block R(x_j), where v = (x_{j-r}, ..., x_{j-1}, x_j)  (the blocks that
                follow on the d^+ circle are R(x_{j-1}), ..., R(x_{j-r}))
successors: ('-', v) -> ('-', v[1:] + z);  ('+', v, i) -> ('+', v, i+1) inside the block, and from the
last dart of the block to ('+', (p,) + v[:-1], 0) for every legal turn (p, v_0).
count(('-', v)) = count(('+', v, i)) = c_v, the number of cyclic occurrences of v in d^- (all words).
c is a circulation on the de Bruijn graph of windows (in = out at every legal r-path) with
[d^-] = 0 in H_1 (M - I is invertible), sum c = 1.  Polygons, pair rows and chi as in lp_allwords.py.
Every certificate projects to a feasible point (validate_memory() checks this on actual certificates),
so min chi >= 0, verified by an exact rational dual vector, rules out every legal f^m-folded fatgraph
with chi < 0, for every boundary.  For r = 1 this refines lp_allwords.py (which forgets the window of
mid-block darts).

usage: python3 lp_memory.py '<phi0 json>' m r [maxval]
       python3 lp_memory.py --validate r cert.json [...]
"""
import sys, json, time, itertools
from fractions import Fraction
from math import lcm
from collections import Counter
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from ffold import inv, inv_word
import lp_allwords as LA


class MTypes:
    def __init__(self, phi, g, r):
        self.phi, self.r = phi, r
        letters = sorted(phi)
        self.L = letters + [x.upper() for x in letters]
        self.R = {x: inv_word(phi[x] if x.islower() else inv_word(phi[x.lower()])) for x in self.L}
        legal = {(x, y) for x in self.L for y in self.L if y != inv(x) and g[inv(x)] != g[y]}
        self.legal = legal
        W = [(x,) for x in self.L]
        for _ in range(r):
            W = [v + (z,) for v in W for z in self.L if (v[-1], z) in legal]
        self.windows = W
        self.widx = {v: i for i, v in enumerate(W)}
        T = [("-", v) for v in W]
        for v in W:
            for i in range(len(self.R[v[-1]])):
                T.append(("+", v, i))
        self.T = T
        self.idx = {t: i for i, t in enumerate(T)}
        self.label, self.fdart, self.kind, self.cw = [], [], [], []
        for t in T:
            if t[0] == "-":
                self.label.append(t[1][0]); self.fdart.append(False); self.kind.append("-")
            else:
                self.label.append(self.R[t[1][-1]][t[2]]); self.fdart.append(t[2] == 0); self.kind.append("+")
            self.cw.append(self.widx[t[1]])
        self.succ = []
        for t in T:
            v = t[1]
            if t[0] == "-":
                s = [self.idx[("-", v[1:] + (z,))] for z in self.L if (v[-1], z) in legal]
            elif t[2] + 1 < len(self.R[v[-1]]):
                s = [self.idx[("+", v, t[2] + 1)]]
            else:
                s = [self.idx[("+", (p,) + v[:-1], 0)] for p in self.L if (p, v[0]) in legal]
            self.succ.append(s)
        self.N = len(T)
        self.bylabel = {x: [i for i in range(self.N) if self.label[i] == x] for x in self.L}


def polygons(TY, g, maxval):
    N = TY.N
    slots = [[] for _ in range(N)]
    for d in range(N):
        for q in TY.bylabel[inv(TY.label[d])]:
            if TY.kind[d] == "-" and TY.kind[q] == "-":
                continue
            for n in TY.succ[q]:
                slots[d].append((q, n))
    out = []
    gl = [g[TY.label[i]] for i in range(N)]
    km = [TY.kind[i] == "-" for i in range(N)]
    fd = TY.fdart
    def rec(darts, sl, gs, nminus, nf):
        d1 = darts[0]; d = darts[-1]; k = len(darts)
        for (q, n) in slots[d]:
            if n == d1:
                if k >= 2 and not (nf and k != 2):
                    out.append(tuple(sl + [(d, q)]))
                continue
            if n <= d1 or k >= maxval:
                continue
            ga = gl[n]
            if ga in gs or (nminus and km[n]):
                continue
            f2 = nf + fd[n]
            if f2 > 1 or (f2 and k >= 2):     # an f-dart only in a 2-gon, at most one f-dart
                continue
            rec(darts + [n], sl + [(d, q)], gs | {ga}, nminus + km[n], f2)
    for d1 in range(N):
        rec([d1], [], {gl[d1]}, int(km[d1]), int(fd[d1]))
    return out


def build(TY, polys):
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
    nw = len(TY.windows)
    ccols = [dict() for _ in range(nw)]
    for i in range(N):
        j = TY.cw[i]
        ccols[j][i] = ccols[j].get(i, 0) - 1
    prefixes = sorted({v[:-1] for v in TY.windows} | {v[1:] for v in TY.windows})
    pidx = {s: r0 + k for k, s in enumerate(prefixes)}
    letters = sorted(TY.phi)
    hom = {x: r0 + len(prefixes) + k for k, x in enumerate(letters)}
    for j, v in enumerate(TY.windows):
        a, b = pidx[v[:-1]], pidx[v[1:]]
        ccols[j][a] = ccols[j].get(a, 0) + 1
        ccols[j][b] = ccols[j].get(b, 0) - 1
        x = v[0]
        h = hom[x.lower()]
        ccols[j][h] = ccols[j].get(h, 0) + (1 if x.islower() else -1)
    nrows = r0 + len(prefixes) + len(letters)
    return nrows, cols, ccols


def solve(TY, polys):
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
    return res, (nrows, cols, ccols)


def exact_dual(polys, built, zfloat):
    """z with (A^T z)_P <= 1 - k_P/2 on polygon columns and (B^T z)_j <= 0 on window columns:
    then chi = sum y_P (1 - k_P/2) >= z^T (A y + B c) = 0 for every feasible point."""
    nrows, cols, ccols = built
    costs = [Fraction(2 - len(P), 2) for P in polys]
    for den in (1, 2, 4, 8, 16, 32, 64, 256, 1024, 4096, 10 ** 6):
        z = [Fraction(float(x)).limit_denominator(den) for x in zfloat[:nrows]]
        if all(sum(val * z[row] for row, val in col.items()) <= cst for col, cst in zip(cols, costs)) and \
           all(sum(val * z[row] for row, val in col.items()) <= 0 for col in ccols):
            return True, den, z
    return False, None, None


def exact_farkas(built):
    """Infeasibility: z, t > 0 with A^T z <= 0 on polygons and B^T z + t <= 0 on windows (sum c = 1)."""
    nrows, cols, ccols = built
    ny, nc = len(cols), len(ccols)
    r, c, v = [], [], []
    for j, col in enumerate(cols):
        for row, val in col.items():
            r.append(j); c.append(row); v.append(float(val))
    for j, col in enumerate(ccols):
        for row, val in col.items():
            r.append(ny + j); c.append(row); v.append(float(val))
        r.append(ny + j); c.append(nrows); v.append(1.0)
    AT = coo_matrix((v, (r, c)), shape=(ny + nc, nrows + 1)).tocsr()
    obj = np.zeros(nrows + 1); obj[nrows] = -1.0
    res = linprog(obj, A_ub=AT, b_ub=np.zeros(ny + nc), bounds=[(-1, 1)] * nrows + [(0, 1)], method="highs")
    if res.status != 0 or res.x[nrows] < 1e-9:
        return False, None
    for den in (1, 2, 3, 4, 6, 8, 12, 16, 24, 64, 256, 1024, 10 ** 6):
        fr = [Fraction(float(x)).limit_denominator(den) for x in res.x]
        t = fr[nrows]
        if t <= 0:
            continue
        if all(sum(val * fr[row] for row, val in col.items()) <= 0 for col in cols) and \
           all(sum(val * fr[row] for row, val in col.items()) + t <= 0 for col in ccols):
            return True, den
    return False, None


def setup(phi0, m, r, maxval=None):
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    if maxval is None:
        maxval = max(2, 2 * min(gp, gn))
    TY = MTypes(phi, g, r)
    polys = polygons(TY, g, maxval)
    return phi, g, TY, polys, maxval


def validate(r, paths):
    bad = 0
    for path in paths:
        cert = json.load(open(path))
        phi, g, TY, polys, maxval = setup(cert["phi0"], cert["power"], r)
        pidx = {P: j for j, P in enumerate(polys)}
        label, tm, nxt = [], [], []
        cnt = Counter()
        for w in cert["minus_words"]:
            L = len(w); start = len(label)
            for i in range(L):
                v = tuple(w[(i + s) % L] for s in range(r + 1))
                label.append(w[i]); tm.append(TY.idx[("-", v)]); cnt[v] += 1
            nxt.extend(start + (i + 1) % L for i in range(L))
            start = len(label)
            for t in range(L - 1, -1, -1):
                v = tuple(w[(t - r + s) % L] for s in range(r + 1))
                blk = TY.R[w[t]]
                for i in range(len(blk)):
                    label.append(blk[i]); tm.append(TY.idx[("+", v, i)])
            n = len(label) - start
            nxt.extend(start + (i + 1) % n for i in range(n))
        p = cert["pairing"]; N = len(label)
        assert len(p) == N
        for d in range(N):
            assert TY.label[tm[d]] == label[d]
            assert tm[nxt[d]] in TY.succ[tm[d]], ("successor", d)
            assert p[p[d]] == d and label[p[d]] == inv(label[d])
        seen, y = set(), Counter()
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
                print(path, "vertex polygon not enumerated", sl[:3], len(sl)); bad += 1
                break
            y[pidx[sl]] += 1
        else:
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
            print(path, "r", r, "maxval", maxval, "darts", N, "vertices", sum(y.values()), "chi", chi,
                  "nonzero rows", len(nz), flush=True)
            bad += bool(nz)
    print("failures", bad)
    return bad


def main(phi0, m, r, maxval=None):
    t0 = time.time()
    phi, g, TY, polys, maxval = setup(phi0, m, r, maxval)
    print("phi0", phi0, "m", m, "r", r, "maxval", maxval, "windows", len(TY.windows), "types", TY.N,
          "polygons", len(polys), "t", round(time.time() - t0, 1), flush=True)
    res, built = solve(TY, polys)
    print("lp status", res.status, res.message, "min chi (sum c = 1):", res.fun, "t", round(time.time() - t0, 1),
          flush=True)
    if res.status == 2:
        ok, den = exact_farkas(built)
        print("RESULT infeasible; exact Farkas certificate:", ok, "denominator", den, flush=True)
    elif res.status == 0 and res.fun < -1e-9:
        x = res.x; ny = len(polys)
        cv = {"".join(TY.windows[j]): round(x[ny + j], 5) for j in range(len(TY.windows)) if x[ny + j] > 1e-9}
        print("RESULT NEGATIVE", res.fun, "window flow:", cv, flush=True)
    elif res.status == 0:
        z = np.asarray(res.eqlin.marginals)
        ok, den, _ = exact_dual(polys, built, z)
        if not ok:
            ok, den, _ = exact_dual(polys, built, -z)
        print("RESULT chi >= 0; exact dual certificate:", ok, "denominator", den, flush=True)
    print("time", round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "--validate":
        sys.exit(validate(int(sys.argv[2]), sys.argv[3:]))
    main(json.loads(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
         int(sys.argv[4]) if len(sys.argv) > 4 else None)
