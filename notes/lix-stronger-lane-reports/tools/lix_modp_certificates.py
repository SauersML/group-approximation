#!/usr/bin/env python3
"""sp-design deliverable 3: certificates for the LIX Step D mod-p model test.

Same constraint set as tools/lix_modp_fast.py, but every constraint row carries the
label (j, i, mu):
    j   = the index of the Wu relation P(gamma_j(W)) = E_j(gamma(W)),
    i   = which reduced-power component P^i of it (weight j + i(p-1)),
    mu  = which monomial h^mu of H^*(Y) the z-part of that component is read on.
The row is a linear form in the unknowns b_nu, nu a monomial of H^*(Y).

Output per case:
  * the Frobenius support of gamma(V)  (weights with c_a(V) != 0),
  * a TRIANGULAR ELIMINATION: repeatedly find a row whose support, after deleting the
    unknowns already forced to 0, is a single unknown; that row kills it.  The order is
    printed as  "(j,i,mu) kills b_nu".
  * whether the target functional L(b) = coeff of z h^d in gamma_r(W) is then identically
    zero on the surviving unknowns (which is the theorem), and if propagation stalls, the
    Gaussian fallback with pivots.
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
    def __init__(self, n, p, d):
        self.n, self.p, self.d, self.l = n, p, list(d), len(d)
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
        p = self.p
        out = {}
        for m, v in a.items():
            terms = [(tuple([0] * self.l), 1)]
            for i in range(self.l):
                new = []
                for mm, c in terms:
                    for j in range(m[i] + 1):
                        coeff = comb(m[i], j) % p
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


def wu_linear_coeff(b, i, p):
    s = (-1) ** (i * (p - 1))
    return (s * (comb(b, i) + (p - 1) * comb(b - 1, i - 1))) % p


def build(n, p, d):
    Rg = Ring(n, p, d)
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

    rows = []          # (label, rowvector)
    for j in range(1, r + 1):
        lhs = Rg.steenrod(Rg.part(bgV, j - n - 1)) if j - n - 1 >= 0 else {}
        rhs = {}
        for a in range(0, min(j, m) + 1):
            bb = j - a
            if bb < 1:
                continue
            inner = {}
            i = 0
            while bb + i * (p - 1) <= r:
                c = wu_linear_coeff(bb, i, p)
                if c:
                    inner = Rg.add(inner, cdelta(bb + i * (p - 1)), c)
                i += 1
            if inner:
                rhs = Rg.add(rhs, Rg.mul_const_aff(PcV[a], inner))
        diff = Rg.add(lhs, rhs, -1)
        for mono, v in diff.items():
            assert v[0] == 0, ("constant term in a z-constraint", j, mono)
            row = v[1:]
            if any(row):
                w = sum(mono)
                num = w + n + 1 - j
                i = num // (p - 1) if (p - 1) and num % (p - 1) == 0 else None
                rows.append(((j, i, mono), row))
    top = tuple(d)
    L = bgV.get(top, [0] * (nv + 1))[1:]
    return Rg, rows, L, dict(m=m, r=r, nv=nv, gV=gV, cV=cV)


def gauss_rank(M, p):
    M = [r[:] for r in M]
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


def certificate(n, p, d, verbose=True, maxprint=40):
    Rg, rows, L, info = build(n, p, d)
    nv = info["nv"]
    monos = Rg.monos
    # Frobenius support of gamma(V)
    supp = sorted({sum(mo) for mo in info["gV"]})
    # triangular propagation
    killed = {}          # var index -> (label, order)
    order = 0
    changed = True
    live = [(lab, row, set(k for k in range(nv) if row[k] % p)) for lab, row in rows]
    while changed:
        changed = False
        for lab, row, sup in live:
            rem = sup - killed.keys()
            if len(rem) == 1:
                v = next(iter(rem))
                killed[v] = (lab, order)
                order += 1
                changed = True
    killset = set(killed)
    Lsupp = set(k for k in range(nv) if L[k] % p)
    forced_by_prop = Lsupp <= killset and any(L)
    rk = gauss_rank([r for _, r in rows], p) if rows else 0
    rk2 = gauss_rank([r for _, r in rows] + [L], p) if rows else (1 if any(L) else 0)
    forced = (rk2 == rk) and any(L)

    print(f"--- n={n} p={p} d={list(d)}   m={info['m']} r={info['r']} unknowns={nv}")
    print(f"    gamma(V) supported in weights {supp}   (p | every weight: "
          f"{all(a % p == 0 for a in supp)})")
    print(f"    rank of the Wu system = {rk}   free = {nv - rk}   "
          f"target in span: {forced}")
    print(f"    triangular propagation kills {len(killed)}/{nv} unknowns; "
          f"target support {'INSIDE' if Lsupp <= killset else 'NOT inside'} the killed set")
    if verbose:
        byres = {}
        for v, (lab, o) in killed.items():
            w = sum(monos[v])
            byres.setdefault(w % p, []).append(v)
        print("    killed unknowns by weight mod p: "
              + ", ".join(f"{k}:{len(v)}" for k, v in sorted(byres.items())))
        allres = {}
        for v in range(nv):
            allres.setdefault(sum(monos[v]) % p, []).append(v)
        print("    all unknowns by weight mod p:    "
              + ", ".join(f"{k}:{len(v)}" for k, v in sorted(allres.items())))
        print("    target L support weights mod p:  "
              + str(sorted({sum(monos[v]) % p for v in Lsupp})))
        # which (j,i) labels are used, and the order
        used = {}
        for v, (lab, o) in killed.items():
            used.setdefault((lab[0], lab[1]), 0)
            used[(lab[0], lab[1])] += 1
        print("    relations used (j, i) -> how many unknowns killed: "
              + str(dict(sorted(used.items()))))
        seq = sorted(killed.items(), key=lambda t: t[1][1])
        print("    elimination order (first %d):" % maxprint)
        for v, (lab, o) in seq[:maxprint]:
            j, i, mu = lab
            print(f"      #{o:3d}  Wu j={j} P^{i} on h^{mu}  kills  b_{monos[v]}"
                  f"  (|nu|={sum(monos[v])}, {sum(monos[v])%p} mod p)")
    return dict(forced=forced, forced_by_prop=forced_by_prop, killed=len(killed), nv=nv,
                rank=rk)


if __name__ == "__main__":
    cases = [
        (2, 2, [2]), (2, 2, [2, 4]),
        (3, 3, [3]), (3, 3, [3, 6]),
        (4, 2, [4]), (5, 5, [5]),
        (6, 2, [6]), (6, 3, [6]), (6, 2, [6, 12]), (6, 3, [6, 12]),
        (7, 7, [7]), (10, 5, [10]),
        # negatives
        (2, 3, [3]), (6, 5, [12]), (6, 7, [6]),
    ]
    if len(sys.argv) > 1:
        cases = [eval(a) for a in sys.argv[1:]]
    for (n, p, d) in cases:
        certificate(n, p, d)
        print()
