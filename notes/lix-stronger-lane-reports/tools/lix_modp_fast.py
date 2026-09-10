#!/usr/bin/env python3
"""Fast model test for the LIX even side (Step D) with mod-p PRIMARY Steenrod operations.
Same question as lix_modp_stepD_modeltest.py, but the Wu constraints are computed through the
virtual-bundle factorisation gamma(W) = gamma(V) * (1 + z b): since z^2 = 0 only the LINEAR part of
the universal polynomial E_b (P(e_b) = E_b(e)) is needed on the delta factor, and that linear part is
  E_b(e) = sum_i (-1)^{i(p-1)} [C(b,i) + (p-1) C(b-1,i-1)] e_{b+i(p-1)}   (mod decomposables).
Constraint j:  z * P((b gamma(V))_{j-n-1}) = sum_{a+b=j, b>=1} P(c_a(V)) * sum_i coeff(b,i) * c_{b+i(p-1)}(delta),
with c_k(delta) = z * (degree k-n-1 part of b).
"""
from itertools import product
import sys

def comb(n, k):
    if k < 0 or k > n: return 0
    r = 1
    for i in range(1, k+1): r = r * (n - k + i) // i
    return r

class Ring:
    def __init__(self, n, p, d):
        self.n, self.p, self.d, self.l = n, p, list(d), len(d)
        self.monos = [tuple(a) for a in product(*[range(di+1) for di in d])]
        self.idx = {m: i for i, m in enumerate(self.monos)}
        self.nv = len(self.monos)
    def zero(self): return {}
    def const(self, c):
        return {tuple([0]*self.l): [c % self.p] + [0]*self.nv} if c % self.p else {}
    # element of H^*(Y): dict mono -> vector [const, b_0, ..., b_{nv-1}] mod p  (z is tracked outside)
    def add(self, a, b, s=1):
        out = {k: v[:] for k, v in a.items()}
        for k, v in b.items():
            w = out.setdefault(k, [0]*(self.nv+1))
            for i in range(self.nv+1): w[i] = (w[i] + s*v[i]) % self.p
        return {k: v for k, v in out.items() if any(v)}
    def mul_const_aff(self, a, b):
        """a constant (only index 0), b affine."""
        p = self.p; out = {}
        for m1, v1 in a.items():
            c1 = v1[0]
            if not c1: continue
            for m2, v2 in b.items():
                m = tuple(x+y for x, y in zip(m1, m2))
                if any(m[i] > self.d[i] for i in range(self.l)): continue
                w = out.setdefault(m, [0]*(self.nv+1))
                for i in range(self.nv+1):
                    if v2[i]: w[i] = (w[i] + c1*v2[i]) % p
        return {k: v for k, v in out.items() if any(v)}
    def steenrod(self, a):
        p = self.p; out = {}
        for m, v in a.items():
            terms = [(tuple([0]*self.l), 1)]
            for i in range(self.l):
                new = []
                for mm, c in terms:
                    for j in range(m[i]+1):
                        coeff = comb(m[i], j) % p
                        if not coeff: continue
                        e = list(mm); e[i] = m[i] + j*(p-1)
                        if e[i] > self.d[i]: continue
                        new.append((tuple(e), (c*coeff) % p))
                terms = new
            for mm, c in terms:
                w = out.setdefault(mm, [0]*(self.nv+1))
                for i in range(self.nv+1):
                    if v[i]: w[i] = (w[i] + c*v[i]) % p
        return {k: v for k, v in out.items() if any(v)}
    def part(self, a, k):
        return {m: v for m, v in a.items() if sum(m) == k}

def run(n, p, d):
    Rg = Ring(n, p, d); m = sum(d); r = n + 1 + m; nv = Rg.nv
    # gamma(V) = prod (1+h_i)^{d_i}: constant element
    gV = {}
    for mono in Rg.monos:
        c = 1
        for i, di in enumerate(d): c = c * comb(di, mono[i])
        c %= p
        if c: gV[mono] = [c] + [0]*nv
    cV = {a: Rg.part(gV, a) for a in range(0, m+1)}
    PcV = {a: Rg.steenrod(cV[a]) for a in range(0, m+1)}
    # b: affine with unit vectors; c_k(delta) = z * b_{k-n-1}
    bvec = {}
    for mono in Rg.monos:
        v = [0]*(nv+1); v[1+Rg.idx[mono]] = 1; bvec[mono] = v
    bpart = {k: Rg.part(bvec, k) for k in range(0, m+1)}
    bgV = Rg.mul_const_aff(gV, bvec)          # b*gamma(V), affine
    def cdelta(k):
        kk = k - n - 1
        return bpart.get(kk, {}) if kk >= 0 else {}
    def coeff(b, i, p):
        s = (-1)**(i*(p-1))
        return (s * (comb(b, i) + (p-1)*comb(b-1, i-1))) % p
    rows = []
    for j in range(1, r+1):
        lhs = Rg.steenrod(Rg.part(bgV, j - n - 1)) if j - n - 1 >= 0 else {}
        rhs = {}
        for a in range(0, min(j, m)+1):
            b = j - a
            if b < 1: continue
            inner = {}
            i = 0
            while b + i*(p-1) <= r:
                c = coeff(b, i, p)
                if c:
                    inner = Rg.add(inner, cdelta(b + i*(p-1)), c)
                i += 1
            if inner:
                rhs = Rg.add(rhs, Rg.mul_const_aff(PcV[a], inner))
        diff = Rg.add(lhs, rhs, -1)
        for mono, v in diff.items():
            assert v[0] == 0, ("constant term in a z-constraint", j, mono)
            row = v[1:]
            if any(row): rows.append(row)
    # target functional L: coefficient of z*h^d in gamma_r(W) = (b gamma(V))_top
    top = tuple(d)
    L = bgV.get(top, [0]*(nv+1))[1:]
    def rank(M):
        M = [r_[:] for r_ in M]; rk = 0; cols = len(M[0]) if M else 0
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
    return ("FORCED" if forced else ("TRIVIAL-L" if not any(L) else "NOT forced"),
            dict(unknowns=nv, rank=rk, free=nv-rk, r=r, m=m))

if __name__ == "__main__":
    import time
    cases = [
        # regression against the slow model
        (2,2,[2]), (2,2,[2,4]), (2,2,[1]), (2,3,[3]), (3,3,[3]), (3,3,[3,6]), (3,2,[2]),
        (4,2,[2]), (4,3,[3]), (5,5,[5]), (5,2,[10]), (6,2,[6]), (6,3,[6]), (6,5,[6]),
        # the actual towers d_j = n 2^j, deeper
        (2,2,[2,4,8]),
        (3,3,[3,6,12]), (3,3,[3,6,12,24]),
        (6,2,[12]), (6,3,[12]), (6,5,[12]), (6,2,[6,12]), (6,3,[6,12]), (6,5,[6,12]), (6,7,[6]), (6,7,[6,12]),
        (6,2,[6,12,24]), (6,3,[6,12,24]), (6,5,[6,12,24]),
        (7,2,[7]), (7,3,[7]), (7,5,[7]), (7,7,[7]), (7,2,[7,14]), (7,3,[7,14]), (7,5,[7,14]), (7,7,[7,14]),
        (10,7,[10]), (10,2,[10]), (10,3,[10]), (10,5,[10]), (10,7,[10,20]),
    ]
    if len(sys.argv) > 1: cases = [eval(a) for a in sys.argv[1:]]
    for (n, p, d) in cases:
        t = time.time()
        try: res = run(n, p, d)
        except Exception as ex: res = ("EXC %s: %s" % (type(ex).__name__, ex), {})
        print("n=%d p=%d d=%s: %s %s (%.1fs)" % (n, p, d, res[0], res[1], time.time()-t), flush=True)
