#!/usr/bin/env python3
"""Model test for the LIX even side (Step D) with mod-p PRIMARY Steenrod operations only.

Setting: N = S^1 x S^{2n+1} x Y, Y = prod CP^{d_i}, H^*(N;F_p) (even part) = H^*(Y)[z]/(z^2),
deg z = 2n+2.  V = 1^{n+1} + sum L_i^{d_i}, rank r = n+1+m, m = sum d_i.  An "allowable" W
restricts to V on the slice, so gamma(W) = gamma(V)(1 + z b) with b in H^*(Y) unknown.
Constraints available to a primary-operation proof: the total power P is a ring hom with
P(h) = h + h^p, P(z) = z (Cartan + instability), and P(gamma(W)) = Phi(gamma(W)) with
Phi the universal Wu polynomial, Phi(prod(1+y)) = prod(1 + y + y^p).
Question: do these force gamma_r(W) = 0 (the top class) for EVERY b?
"""
from fractions import Fraction
from itertools import product
from functools import reduce
def comb(n, k):
    if k < 0 or k > n: return 0
    r = 1
    for i in range(1, k+1): r = r * (n - k + i) // i
    return r
import sys

def phi_universal(R, p):
    def wdeg(m): return sum((j+1)*a for j, a in enumerate(m))
    def add(a, b, s=1):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, 0) + s*v
            if out[k] == 0: del out[k]
        return out
    def mul(a, b):
        out = {}
        for k1, v1 in a.items():
            for k2, v2 in b.items():
                k = tuple(x+y for x, y in zip(k1, k2))
                if wdeg(k) > R: continue
                out[k] = out.get(k, 0) + v1*v2
        return {k: v for k, v in out.items() if v != 0}
    def scal(a, c): return {k: v*c for k, v in a.items()} if c != 0 else {}
    zero = tuple([0]*R)
    def e(j):
        if j == 0: return {zero: Fraction(1)}
        if j > R: return {}
        m = [0]*R; m[j-1] = 1
        return {tuple(m): Fraction(1)}
    ps = {}
    for j in range(1, R+1):
        acc = scal(e(j), Fraction((-1)**(j-1) * j))
        for i in range(1, j):
            acc = add(acc, scal(mul(e(i), ps[j-i]), Fraction((-1)**(i-1))))
        ps[j] = acc
    def p_(j): return ps[j] if j <= R else {}
    Ps = {}
    for j in range(1, R+1):
        acc = {}
        for i in range(0, j+1):
            J = j + i*(p-1)
            if J > R: break
            acc = add(acc, scal(p_(J), Fraction(comb(j, i))))
        Ps[j] = acc
    Es = {0: {zero: Fraction(1)}}
    for k in range(1, R+1):
        acc = {}
        for i in range(1, k+1):
            acc = add(acc, scal(mul(Es[k-i], Ps[i]), Fraction((-1)**(i-1))))
        Es[k] = scal(acc, Fraction(1, k))
    outs = {}
    for k in range(0, R+1):
        out = {}
        for kk, v in Es[k].items():
            assert v.denominator == 1, ("non-integral E coefficient", k, kk, v)
            c = int(v) % p
            if c: out[kk] = c
        outs[k] = out
    return outs

class Ring:
    """H^*(Y)[z]/(z^2) over F_p with coefficients that are affine forms in unknowns b_mu."""
    def __init__(self, n, p, d):
        self.n, self.p, self.d = n, p, list(d)
        self.l = len(d)
        self.monos = [tuple(a) for a in product(*[range(di+1) for di in d])]
        self.idx = {m: i for i, m in enumerate(self.monos)}   # b_mu index
    def deg(self, m, zeta): return sum(m) + zeta*(self.n+1)        # in units of 2
    # element: dict {(m, zeta): {var: coeff}} with var 'c' or int
    def add(self, a, b, s=1):
        out = {k: dict(v) for k, v in a.items()}
        for k, form in b.items():
            f = out.setdefault(k, {})
            for var, c in form.items():
                f[var] = (f.get(var, 0) + s*c) % self.p
                if f[var] == 0: del f[var]
            if not f: del out[k]
        return out
    def mul(self, a, b):
        p = self.p
        out = {}
        for (m1, z1), f1 in a.items():
            for (m2, z2), f2 in b.items():
                if z1 + z2 > 1: continue
                m = tuple(x+y for x, y in zip(m1, m2))
                if any(m[i] > self.d[i] for i in range(self.l)): continue
                c1 = 'c' in f1 and len(f1) == 1
                c2 = 'c' in f2 and len(f2) == 1
                if not c1 and not c2:
                    raise RuntimeError("quadratic term without z^2")
                form = out.setdefault((m, z1+z2), {})
                if c1:
                    for var, c in f2.items():
                        form[var] = (form.get(var, 0) + f1['c']*c) % p
                else:
                    for var, c in f1.items():
                        form[var] = (form.get(var, 0) + f2['c']*c) % p
        return {k: {v: c for v, c in f.items() if c} for k, f in out.items() if any(f.values())}
    def const(self, c):
        z = tuple([0]*self.l)
        return {(z, 0): {'c': c % self.p}} if c % self.p else {}
    def one(self): return self.const(1)
    def power(self, a, k):
        out = self.one()
        for _ in range(k): out = self.mul(out, a)
        return out
    def steenrod(self, a):
        """total P: ring hom, P(h_i) = h_i + h_i^p, P(z) = z."""
        p = self.p
        out = {}
        for (m, zeta), form in a.items():
            # expand prod_i (h_i + h_i^p)^{m_i}
            terms = [((tuple([0]*self.l), zeta), 1)]
            for i in range(self.l):
                new = []
                for (mm, zz), c in terms:
                    for j in range(m[i]+1):
                        coeff = comb(m[i], j) % p
                        if not coeff: continue
                        e = list(mm); e[i] = m[i] + j*(p-1)
                        if e[i] > self.d[i]: continue
                        new.append(((tuple(e), zz), (c*coeff) % p))
                terms = new
            for key, c in terms:
                f = out.setdefault(key, {})
                for var, cc in form.items():
                    f[var] = (f.get(var, 0) + c*cc) % p
        return {k: {v: c for v, c in f.items() if c} for k, f in out.items() if any(f.values())}
    def graded_part(self, a, j):
        return {k: v for k, v in a.items() if self.deg(*k) == j}

def run(n, p, d, verbose=False):
    Rg = Ring(n, p, d)
    m = sum(d); r = n + 1 + m
    Es = phi_universal(r, p)
    # gamma(V) = prod (1+h_i)^{d_i}
    gV = Rg.one()
    for i, di in enumerate(d):
        h = {(tuple(1 if j == i else 0 for j in range(Rg.l)), 0): {'c': 1}}
        gV = Rg.mul(gV, Rg.power(Rg.add(Rg.one(), h), di))
    # b = sum b_mu h^mu ; zb
    zb = {}
    for mu in Rg.monos:
        zb[(mu, 1)] = {Rg.idx[mu]: 1}
    gW = Rg.mul(gV, Rg.add(Rg.one(), zb))
    gj = {j: Rg.graded_part(gW, j) for j in range(0, r+1)}
    nv = len(Rg.monos)
    rows = []
    for jdeg in range(1, r+1):
        EW = {}
        for exps, c in Es[jdeg].items():
            term = Rg.const(c)
            for j, a in enumerate(exps):
                if a: term = Rg.mul(term, Rg.power(gj[j+1], a))
            EW = Rg.add(EW, term)
        diff = Rg.add(Rg.steenrod(gj[jdeg]), EW, -1)
        bad = [(k, f) for k, f in diff.items() if 'c' in f]
        if bad:
            return dict(status="MODEL ERROR: Wu identity fails on V at j=%d" % jdeg, detail=bad[:3])
        for k, f in diff.items():
            row = [0]*nv
            for var, c in f.items(): row[var] = c % p
            if any(row): rows.append(row)
    # target functional: coefficient of z*h^d in gamma_r(W) = sum_mu b_mu gV[d-mu]
    top = tuple(d)
    L = [0]*nv
    for mu in Rg.monos:
        rest = tuple(di - mi for di, mi in zip(top, mu))
        c = gV.get((rest, 0), {}).get('c', 0)
        L[Rg.idx[mu]] = c % p
    def rank(M):
        M = [r[:] for r in M]; rk = 0; cols = len(M[0]) if M else 0
        for c in range(cols):
            piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
            if piv is None: continue
            M[rk], M[piv] = M[piv], M[rk]
            inv = pow(M[rk][c], p-2, p)
            M[rk] = [(x*inv) % p for x in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c] % p:
                    f = M[i][c]; M[i] = [(x - f*y) % p for x, y in zip(M[i], M[rk])]
            rk += 1
        return rk
    rk = rank(rows) if rows else 0
    rk2 = rank(rows + [L])
    forced = (rk2 == rk) and any(L)
    return dict(status="FORCED" if forced else ("TRIVIAL-L" if not any(L) else "NOT forced"),
                unknowns=nv, constraints=len(rows), rank=rk, free=nv-rk, r=r, m=m)

if __name__ == "__main__":
    cases = [
        # calibration (must be FORCED: the F2 proof exists)
        (2,2,[2]), (2,2,[4]), (2,2,[2,4]), (2,2,[]),
        # negative controls: odd d at p=2 (F2 proof needs even d); (2,3) must NOT force (Bott: order 2)
        (2,2,[1]), (2,2,[3]), (2,3,[3]), (2,3,[]),
        # n = 3
        (3,3,[3]), (3,3,[6]), (3,3,[3,6]), (3,3,[]), (3,2,[2]), (3,2,[6]), (3,2,[]),
        # n = 4
        (4,2,[2]), (4,2,[4]), (4,2,[8]), (4,2,[]), (4,3,[3]), (4,3,[4]), (4,3,[4,8]), (4,3,[]),
        # n = 5, 6
        (5,5,[5]), (5,5,[]), (5,2,[5]), (5,2,[10]), (5,3,[5]),
        (6,2,[6]), (6,3,[6]), (6,5,[6]), (6,5,[5]), (6,5,[]), (6,3,[]), (6,2,[]),
    ]
    if len(sys.argv) > 1:
        cases = [eval(a) for a in sys.argv[1:]]
    for (n, p, d) in cases:
        try:
            res = run(n, p, d)
        except Exception as ex:
            res = dict(status=f"EXC {type(ex).__name__}: {ex}")
        print(f"n={n} p={p} d={d}: {res}", flush=True)
