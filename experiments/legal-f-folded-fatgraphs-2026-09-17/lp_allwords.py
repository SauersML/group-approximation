"""Word-free certificate LP: all boundaries d^- at once.

A legal f-folded fatgraph X (conventions of lp5.py) has boundary d^- = union of legal
cyclic words and d^+ = their images f(w)^{-1}.  Project every dart to a TYPE:
  ('-', x, y)    a d^- letter x followed on its circle by y           count c_xy
  ('+', x, i)    letter i (0 <= i <= l(x)-2) of the block R(x) = f(x)^{-1}  count n_x
  ('L', p, x)    the last letter of block R(x), whose circle continues with block R(p)
                 (p precedes x in w)                                    count c_px
where c_xy = number of occurrences of the turn xy in d^-, n_x = sum_y c_xy.  Type
successor relation: ('-',x,y) -> ('-',y,z); ('+',x,i) -> ('+',x,i+1) or ('L',p,x);
('L',p,x) -> first dart of block R(p).  An f-dart is a first dart of a block.
Every vertex polygon of X projects to a cyclic list of type slots (d_s -> q_s) with
label(q_s) = inv(label(d_s)), d_{s+1} a successor type of q_s, directions in distinct gates,
at most one d^- dart, an f-dart only in a 2-gon, no slot pairing two d^- darts.
Valid linear constraints (y_P = number of vertices of type P):
  each type tau:           sum_P y_P #{s : d_s = tau} = count(tau)(c)
  each type pair {tau,s}:  #slots tau->sigma = #slots sigma->tau
  c a circulation on legal turns with [w] = 0 in H_1, sum c = 1.
chi(X) = sum_P y_P (1 - k_P/2).  If the LP minimum is >= 0, no legal f-folded fatgraph
with chi < 0 exists, for ANY boundary.  exact_dual() verifies a rational dual certificate:
z with (A^T z)_P <= 1 - k_P/2 on every polygon column and (B^T z)_j <= 0 on every c column,
for the homogeneous system (A y + B c = 0), which gives chi >= 0 for every feasible point.

usage: python3 lp_allwords.py '<phi json>' m [maxval]
"""
import sys, json, time, itertools
from fractions import Fraction
from math import lcm
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from ffold import inv, inv_word, gate_of, legal_turn


def power(phi, m):
    letters = sorted(phi)
    def ap(w):
        return "".join(phi[x] if x.islower() else inv_word(phi[x.lower()]) for x in w)
    res = {x: x for x in letters}
    for _ in range(m):
        res = {x: ap(res[x]) for x in letters}
    return res


def gates(phi):
    letters = sorted(phi)
    D = {}
    for x in letters:
        D[x] = phi[x][0]
        D[x.upper()] = inv(phi[x][-1])
    g = {}
    for d in D:
        e = d
        for _ in range(4 * len(D) + 4):
            e = D[e]
        g[d] = e
    # canonical gate label: the periodic direction reached after many steps
    return g


class Types:
    def __init__(self, phi, g):
        self.phi = phi
        letters = sorted(phi)
        self.L = letters + [x.upper() for x in letters]
        R = {}
        for x in self.L:
            blk = phi[x] if x.islower() else inv_word(phi[x.lower()])
            R[x] = inv_word(blk)
        self.R = R
        self.turns = [(x, y) for x in self.L for y in self.L
                      if y != inv(x) and g[inv(x)] != g[y]]
        self.tidx = {t: i for i, t in enumerate(self.turns)}
        T = []
        for (x, y) in self.turns:
            T.append(("-", x, y))
        for x in self.L:
            for i in range(len(R[x]) - 1):
                T.append(("+", x, i))
        for (p, x) in self.turns:
            T.append(("L", p, x))
        self.T = T
        self.idx = {t: i for i, t in enumerate(T)}
        self.label = []
        self.fdart = []
        self.kind = []
        for t in T:
            if t[0] == "-":
                self.label.append(t[1]); self.fdart.append(False); self.kind.append("-")
            elif t[0] == "+":
                self.label.append(R[t[1]][t[2]]); self.fdart.append(t[2] == 0); self.kind.append("+")
            else:
                self.label.append(R[t[2]][-1]); self.fdart.append(len(R[t[2]]) == 1); self.kind.append("+")
        self.succ = []
        for t in T:
            if t[0] == "-":
                s = [self.idx[("-", t[2], z)] for z in self.L if (t[2], z) in self.tidx]
            elif t[0] == "+":
                x, i = t[1], t[2]
                if i + 1 <= len(R[x]) - 2:
                    s = [self.idx[("+", x, i + 1)]]
                else:
                    s = [self.idx[("L", p, x)] for p in self.L if (p, x) in self.tidx]
            else:
                p = t[1]
                if len(R[p]) >= 2:
                    s = [self.idx[("+", p, 0)]]
                else:
                    s = [self.idx[("L", pp, p)] for pp in self.L if (pp, p) in self.tidx]
            self.succ.append(s)
        self.N = len(T)
        self.bylabel = {x: [i for i in range(self.N) if self.label[i] == x] for x in self.L}

    def count_coeffs(self, i):
        """count(type i) as dict turn_index -> coefficient."""
        t = self.T[i]
        if t[0] == "-":
            return {self.tidx[(t[1], t[2])]: 1}
        if t[0] == "+":
            return {self.tidx[(t[1], y)]: 1 for y in self.L if (t[1], y) in self.tidx}
        return {self.tidx[(t[1], t[2])]: 1}


def polygons(TY, g, maxval):
    N = TY.N
    slots = [[] for _ in range(N)]     # d -> list of (q, successor n)
    for d in range(N):
        for q in TY.bylabel[inv(TY.label[d])]:
            if TY.kind[d] == "-" and TY.kind[q] == "-":
                continue
            for n in TY.succ[q]:
                slots[d].append((q, n))
    out = []
    def rec(darts, sl, gs, nminus, nf):
        d1 = darts[0]; d = darts[-1]; k = len(darts)
        for (q, n) in slots[d]:
            if n == d1:
                if k >= 2 and not (nf and k != 2):
                    out.append(tuple(sl + [(d, q)]))
                continue
            if n <= d1 or k >= maxval:
                continue
            ga = g[TY.label[n]]
            if ga in gs:
                continue
            m2 = nminus + (TY.kind[n] == "-")
            f2 = nf + TY.fdart[n]
            if m2 > 1 or f2 > 1 or (f2 and k >= 2) or (nf and k >= 2):
                continue
            rec(darts + [n], sl + [(d, q)], gs | {ga}, m2, f2)
    for d1 in range(N):
        rec([d1], [], {g[TY.label[d1]]}, int(TY.kind[d1] == "-"), int(TY.fdart[d1]))
    return out


def build(TY, polys):
    """Homogeneous system A y + B c = 0 plus normalisation sum c = 1."""
    N = TY.N
    nt = len(TY.turns)
    pairs = {}
    cols = []
    for P in polys:
        col = {}
        for (d, q) in P:
            col[d] = col.get(d, 0) + 1
            key = (min(d, q), max(d, q))
            r = pairs.setdefault(key, N + len(pairs))
            col[r] = col.get(r, 0) + (1 if d < q else -1)
        cols.append(col)
    r0 = N + len(pairs)
    letters = sorted(TY.phi)
    # c columns: -count(type) on type rows, circulation rows, homology rows
    ccols = [dict() for _ in range(nt)]
    for i in range(N):
        for j, v in TY.count_coeffs(i).items():
            ccols[j][i] = ccols[j].get(i, 0) - v
    circ = {x: r0 + k for k, x in enumerate(TY.L)}
    hom = {x: r0 + len(TY.L) + k for k, x in enumerate(letters)}
    for j, (x, y) in enumerate(TY.turns):
        ccols[j][circ[x]] = ccols[j].get(circ[x], 0) + 1      # out of x
        ccols[j][circ[y]] = ccols[j].get(circ[y], 0) - 1      # into y
        if x.islower():
            ccols[j][hom[x]] = ccols[j].get(hom[x], 0) + 1
        else:
            ccols[j][hom[x.lower()]] = ccols[j].get(hom[x.lower()], 0) - 1
    nrows = r0 + len(TY.L) + len(letters)
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
    # normalisation row
    for j in range(nc):
        r.append(nrows); c.append(ny + j); v.append(1.0)
    A = coo_matrix((v, (r, c)), shape=(nrows + 1, ny + nc)).tocsr()
    b = np.zeros(nrows + 1); b[nrows] = 1.0
    cost = np.array([1.0 - len(P) / 2.0 for P in polys] + [0.0] * nc)
    res = linprog(cost, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    return res, (nrows, cols, ccols, A)


def exact_dual(TY, polys, built, zfloat):
    """Round a floating dual z (rows 0..nrows-1) and verify chi >= 0 exactly."""
    nrows, cols, ccols, _ = built
    costs = [Fraction(2 - len(P), 2) for P in polys]
    def check(z):
        for P, col, cst in zip(polys, cols, costs):
            if sum(val * z[row] for row, val in col.items()) > cst:
                return False
        for col in ccols:
            if sum(val * z[row] for row, val in col.items()) > 0:
                return False
        return True
    for den in (1, 2, 4, 8, 16, 64, 256, 1024, 10 ** 6):
        z = [Fraction(float(x)).limit_denominator(den) for x in zfloat[:nrows]]
        if check(z):
            return True, den
    return False, None


def main(phi0, m, maxval=None):
    phi = power(phi0, m)
    g = gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    if maxval is None:
        maxval = max(2, 2 * min(gp, gn))
    t0 = time.time()
    TY = Types(phi, g)
    polys = polygons(TY, g, maxval)
    print("phi0", phi0, "m", m, "block lengths", [len(phi[x]) for x in sorted(phi)],
          "gates", {d: g[d] for d in sorted(g)}, "maxval", maxval,
          "types", TY.N, "turns", len(TY.turns), "polygons", len(polys),
          "t", round(time.time() - t0, 1), flush=True)
    used = {d for P in polys for (d, q) in P}
    unc = [TY.T[i] for i in range(TY.N) if i not in used]
    print("types in no polygon:", len(unc), unc[:12], flush=True)
    res, built = solve(TY, polys)
    print("lp status", res.status, res.message, "min chi (sum c = 1):", res.fun,
          "t", round(time.time() - t0, 1), flush=True)
    if res.status == 0 and res.fun < -1e-9:
        x = res.x; ny = len(polys)
        cvals = {TY.turns[j]: round(x[ny + j], 5) for j in range(len(TY.turns)) if x[ny + j] > 1e-9}
        print("turn flow:", cvals)
        sup = sorted(((x[j], polys[j]) for j in range(ny) if x[j] > 1e-9), reverse=True)[:15]
        for val, P in sup:
            print(round(val, 5), [(TY.T[d], TY.T[q]) for d, q in P])
    elif res.status == 0:
        z = res.eqlin.marginals
        ok, den = exact_dual(TY, polys, built, -np.asarray(z))
        if not ok:
            ok, den = exact_dual(TY, polys, built, np.asarray(z))
        print("exact dual certificate chi >= 0:", ok, "denominator", den, flush=True)
    return res


if __name__ == "__main__":
    phi0 = json.loads(sys.argv[1]); m = int(sys.argv[2])
    mv = int(sys.argv[3]) if len(sys.argv) > 3 else None
    main(phi0, m, mv)


def farkas_infeasible(TY, polys, built, verbose=False):
    """Infeasibility of {A y + B c = 0, sum c = 1, y, c >= 0}: find z, t > 0 with
    A^T z <= 0 (polygon columns) and B^T z + t <= 0 (c columns); verify exactly."""
    nrows, cols, ccols, _ = built
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
    bounds = [(-1, 1)] * nrows + [(0, 1)]
    res = linprog(obj, A_ub=AT, b_ub=np.zeros(ny + nc), bounds=bounds, method="highs")
    if res.status != 0 or res.x[nrows] < 1e-9:
        return False, None, None
    def check(z, t):
        if t <= 0:
            return False
        for col in cols:
            if sum(val * z.get(row, 0) for row, val in col.items()) > 0:
                return False
        for col in ccols:
            if sum(val * z.get(row, 0) for row, val in col.items()) + t > 0:
                return False
        return True
    for den in (1, 2, 3, 4, 6, 8, 12, 16, 24, 64, 256, 1024, 10 ** 6):
        fr = [Fraction(float(x)).limit_denominator(den) for x in res.x]
        L = 1
        for x in fr:
            L = lcm(L, x.denominator)
        z = {i: int(fr[i] * L) for i in range(nrows) if fr[i] != 0}
        t = int(fr[nrows] * L)
        if check(z, t):
            return True, den, (z, t)
    return False, None, res.x
