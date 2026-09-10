#!/usr/bin/env python3
"""sp-design, task (a) for the lead: the kappa-sweep of the section 1.4 model test.

tools/lix_modp_fast.py with P(h) = h + kappa*h^p instead of P(h) = h + h^p, for every
kappa in F_p^x.  Two things change together, and BOTH are changed here:

  * the Steenrod ring homomorphism on H^*(Y):  P(h^m) = (h + kappa h^p)^m
      = sum_j C(m,j) kappa^j h^{m + j(p-1)} ;
  * the universal Wu polynomials:  E_j(e) = e_j(y + kappa y^p), whose linear part is
      E_b(e) = sum_i (-1)^{i(p-1)} C(b-1,i) kappa^i e_{b+i(p-1)}  (mod decomposables).

Expected (and this is a theorem, not a guess): P'^i := kappa^{-i} P^i satisfies every
axiom with P'(h) = h + h^p, the total P' is still a ring homomorphism because
kappa^{-(a+b)} = kappa^{-a} kappa^{-b}, and the per-j Wu relation of the kappa-family is
the kappa = 1 relation with its weight-(j + i(p-1)) component multiplied by kappa^i.
Multiplying the rows of a homogeneous linear system by nonzero scalars does not move its
solution space, so the FORCED/NOT verdict must be independent of kappa.  This script is
the confirmation for the record.
"""
from itertools import product
import sys


def comb(n, k):
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(1, k + 1):
        r = r * (n - k + i) // i
    return r


class Ring:
    def __init__(self, n, p, d, kappa):
        self.n, self.p, self.d, self.l = n, p, list(d), len(d)
        self.kappa = kappa % p
        self.monos = [tuple(a) for a in product(*[range(di + 1) for di in d])]
        self.idx = {m: i for i, m in enumerate(self.monos)}
        self.nv = len(self.monos)

    def add(self, a, b, s=1):
        out = {k: v[:] for k, v in a.items()}
        for k, v in b.items():
            w = out.setdefault(k, [0] * (self.nv + 1))
            for i in range(self.nv + 1):
                w[i] = (w[i] + s * v[i]) % self.p
        return {k: v for k, v in out.items() if any(v)}

    def mul_const_aff(self, a, b):
        p = self.p
        out = {}
        for m1, v1 in a.items():
            c1 = v1[0]
            if not c1:
                continue
            for m2, v2 in b.items():
                m = tuple(x + y for x, y in zip(m1, m2))
                if any(m[i] > self.d[i] for i in range(self.l)):
                    continue
                w = out.setdefault(m, [0] * (self.nv + 1))
                for i in range(self.nv + 1):
                    if v2[i]:
                        w[i] = (w[i] + c1 * v2[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    def steenrod(self, a):
        """total P with P(h_i) = h_i + kappa h_i^p."""
        p, kap = self.p, self.kappa
        out = {}
        for m, v in a.items():
            terms = [(tuple([0] * self.l), 1)]
            for i in range(self.l):
                new = []
                for mm, c in terms:
                    for j in range(m[i] + 1):
                        coeff = (comb(m[i], j) * pow(kap, j, p)) % p
                        if not coeff:
                            continue
                        e = list(mm)
                        e[i] = m[i] + j * (p - 1)
                        if e[i] > self.d[i]:
                            continue
                        new.append((tuple(e), (c * coeff) % p))
                terms = new
            for mm, c in terms:
                w = out.setdefault(mm, [0] * (self.nv + 1))
                for i in range(self.nv + 1):
                    if v[i]:
                        w[i] = (w[i] + c * v[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    def part(self, a, k):
        return {m: v for m, v in a.items() if sum(m) == k}


def run(n, p, d, kappa):
    Rg = Ring(n, p, d, kappa)
    m = sum(d)
    r = n + 1 + m
    nv = Rg.nv
    gV = {}
    for mono in Rg.monos:
        c = 1
        for i, di in enumerate(d):
            c = c * comb(di, mono[i])
        c %= p
        if c:
            gV[mono] = [c] + [0] * nv
    cV = {a: Rg.part(gV, a) for a in range(0, m + 1)}
    PcV = {a: Rg.steenrod(cV[a]) for a in range(0, m + 1)}
    bvec = {}
    for mono in Rg.monos:
        v = [0] * (nv + 1)
        v[1 + Rg.idx[mono]] = 1
        bvec[mono] = v
    bpart = {k: Rg.part(bvec, k) for k in range(0, m + 1)}
    bgV = Rg.mul_const_aff(gV, bvec)

    def cdelta(k):
        kk = k - n - 1
        return bpart.get(kk, {}) if kk >= 0 else {}

    def coeff(b, i):
        """linear part of E_b for P(y) = y + kappa y^p."""
        s = (-1) ** (i * (p - 1))
        return (s * comb(b - 1, i) * pow(Rg.kappa, i, p)) % p

    rows = []
    for j in range(1, r + 1):
        lhs = Rg.steenrod(Rg.part(bgV, j - n - 1)) if j - n - 1 >= 0 else {}
        rhs = {}
        for a in range(0, min(j, m) + 1):
            b = j - a
            if b < 1:
                continue
            inner = {}
            i = 0
            while b + i * (p - 1) <= r:
                c = coeff(b, i)
                if c:
                    inner = Rg.add(inner, cdelta(b + i * (p - 1)), c)
                i += 1
            if inner:
                rhs = Rg.add(rhs, Rg.mul_const_aff(PcV[a], inner))
        diff = Rg.add(lhs, rhs, -1)
        for mono, v in diff.items():
            assert v[0] == 0, ("constant term in a z-constraint", j, mono)
            row = v[1:]
            if any(row):
                rows.append(row)
    top = tuple(d)
    L = bgV.get(top, [0] * (nv + 1))[1:]

    def rank(M):
        M = [r_[:] for r_ in M]
        rk = 0
        cols = len(M[0]) if M else 0
        for c in range(cols):
            piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            inv = pow(M[rk][c], p - 2, p)
            M[rk] = [(x * inv) % p for x in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c] % p:
                    f = M[i][c]
                    M[i] = [(x - f * y) % p for x, y in zip(M[i], M[rk])]
            rk += 1
        return rk

    rk = rank(rows) if rows else 0
    rk2 = rank(rows + [L])
    forced = (rk2 == rk) and any(L)
    return ("FORCED" if forced else ("TRIVIAL-L" if not any(L) else "NOT forced")), rk, nv - rk


if __name__ == "__main__":
    # the table of the program note, plus the negative controls
    cases = [
        (2, 2, [2]), (2, 2, [2, 4]), (2, 2, [2, 4, 8]),
        (2, 3, [3]),
        (3, 3, [3]), (3, 3, [6]), (3, 3, [3, 6]),
        (3, 2, [2]), (3, 2, [6]),
        (4, 2, [2]), (4, 2, [4]), (4, 2, [8]), (4, 3, [3]), (4, 3, [4]),
        (5, 5, [5]),
        (6, 2, [6]), (6, 2, [12]), (6, 3, [6]), (6, 3, [12]),
        (6, 5, [6]), (6, 5, [12]), (6, 7, [6]),
        (7, 7, [7]), (7, 2, [7]), (7, 3, [7]), (7, 5, [7]),
        (10, 7, [10]), (11, 11, [11]),
    ]
    if len(sys.argv) > 1:
        cases = [eval(a) for a in sys.argv[1:]]
    ndiff = 0
    for (n, p, d) in cases:
        verdicts = {}
        for kappa in range(1, p):
            try:
                v, rk, free = run(n, p, d, kappa)
            except Exception as ex:
                v, rk, free = f"EXC {type(ex).__name__}", -1, -1
            verdicts[kappa] = (v, rk, free)
        allsame = len({v for v in verdicts.values()}) == 1
        if not allsame:
            ndiff += 1
        base = verdicts[1]
        print(f"n={n} p={p} d={d}: kappa=1 -> {base[0]} (rank {base[1]}, free {base[2]}); "
              f"identical for every kappa in F_p^x: {allsame}"
              + ("" if allsame else f"   !!! {verdicts}"), flush=True)
    print()
    print("cases where the verdict depended on kappa:", ndiff, "of", len(cases))
