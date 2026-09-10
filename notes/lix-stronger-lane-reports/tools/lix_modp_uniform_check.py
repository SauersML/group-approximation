#!/usr/bin/env python3
"""sp-design deliverable 3: model-test EVERY lemma of the uniform Step D argument.

The uniform argument (p | n, p | d_i for every i):

 L0  Wu for V, formal:  P(gamma_a(V)) = E_a(gamma(V)) for every a.
 L1  Frobenius:         gamma(V) = prod_i (1 + h_i^p)^{d_i/p}.
 L2  Frobenius on P:    P(gamma(V)) = prod_i (1 + h_i^p + h_i^{p^2})^{d_i/p}.
 L3a                    gamma_a(V) = 0 unless p | a.
 L3b                    P^i(gamma_a(V)) = 0 unless p | i.
 L4a linear Wu:         E_b(e) = sum_i (-1)^{i(p-1)} C(b-1,i) e_{b+i(p-1)}  mod decomposables.
 L4  z-part:            P(B_{j-n-1}) = sum_{a+b'=j,b'>=1} sum_{i'} (-1)^{i'(p-1)} C(b'-1,i')
                          P(gamma_a(V)) frak b_{b'-n-1+i'(p-1)},   B = gamma(V) b.
 L5  diagonal j = i+1:  instability kills the left side, and the weight-(ip-n) component is
                          0 = frak b_{ip-n} + (terms in frak b_{k'}, k' < ip-n, k' = ip-n mod p),
                        the leading coefficient being exactly 1 (C(i,i) = 1).
 L6  induction:         p | n  =>  frak b_k = 0 for every k = 0 mod p, 0 <= k <= m.
 L7  assembly:          gamma_r(W) = z * sum_{p|a} gamma_a(V) frak b_{m-a} = 0.

Every one of L0..L7 is checked symbolically over F_p for a list of (n, p, d).
Also: a regression of tools/lix_modp_fast.py against its slow twin.
"""
from itertools import product
import sys
from fractions import Fraction


def comb(n, k):
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(1, k + 1):
        r = r * (n - k + i) // i
    return r


# ---------------------------------------------------------------- truncated polynomial ring

class Poly:
    """F_p[h_1..h_l]/(h_i^{d_i+1}), elements as dict mono -> coeff."""

    def __init__(self, p, d):
        self.p, self.d, self.l = p, list(d), len(d)

    def one(self):
        return {tuple([0] * self.l): 1}

    def add(self, a, b, s=1):
        out = dict(a)
        for k, v in b.items():
            out[k] = (out.get(k, 0) + s * v) % self.p
            if out[k] == 0:
                del out[k]
        return out

    def mul(self, a, b):
        out = {}
        for k1, v1 in a.items():
            for k2, v2 in b.items():
                k = tuple(x + y for x, y in zip(k1, k2))
                if any(k[i] > self.d[i] for i in range(self.l)):
                    continue
                out[k] = (out.get(k, 0) + v1 * v2) % self.p
        return {k: v for k, v in out.items() if v}

    def scal(self, a, c):
        c %= self.p
        return {k: (v * c) % self.p for k, v in a.items() if (v * c) % self.p} if c else {}

    def pow(self, a, e):
        out = self.one()
        base = dict(a)
        while e:
            if e & 1:
                out = self.mul(out, base)
            base = self.mul(base, base)
            e >>= 1
        return out

    def gen(self, i, e=1):
        m = [0] * self.l
        m[i] = e
        return {tuple(m): 1} if e <= self.d[i] else {}

    def part(self, a, w):
        return {k: v for k, v in a.items() if sum(k) == w}

    def steenrod_total(self, a):
        """total P: ring hom with P(h_i) = h_i + h_i^p."""
        out = {}
        for m, v in a.items():
            terms = [(tuple([0] * self.l), 1)]
            for i in range(self.l):
                new = []
                for mm, c in terms:
                    for j in range(m[i] + 1):
                        cc = comb(m[i], j) % self.p
                        if not cc:
                            continue
                        e = list(mm)
                        e[i] = m[i] + j * (self.p - 1)
                        if e[i] > self.d[i]:
                            continue
                        new.append((tuple(e), (c * cc) % self.p))
                terms = new
            for mm, c in terms:
                out[mm] = (out.get(mm, 0) + c * v) % self.p
        return {k: v for k, v in out.items() if v}

    def steenrod_i(self, a, i):
        """P^i on a homogeneous a of weight w: the weight-(w + i(p-1)) part of P(a)."""
        ws = {sum(k) for k in a}
        assert len(ws) <= 1, "steenrod_i needs a homogeneous input"
        if not a:
            return {}
        w = ws.pop()
        return self.part(self.steenrod_total(a), w + i * (self.p - 1))


# ---------------------------------------------------------------- universal Wu polynomials

def phi_universal(R, p):
    """E_k as a polynomial in e_1..e_R: dict exps -> coeff mod p (exps[j] = power of e_{j+1})."""
    def wdeg(m):
        return sum((j + 1) * a for j, a in enumerate(m))

    def add(a, b, s=1):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, 0) + s * v
            if out[k] == 0:
                del out[k]
        return out

    def mul(a, b):
        out = {}
        for k1, v1 in a.items():
            for k2, v2 in b.items():
                k = tuple(x + y for x, y in zip(k1, k2))
                if wdeg(k) > R:
                    continue
                out[k] = out.get(k, 0) + v1 * v2
        return {k: v for k, v in out.items() if v != 0}

    def scal(a, c):
        return {k: v * c for k, v in a.items()} if c != 0 else {}

    zero = tuple([0] * R)

    def e(j):
        if j == 0:
            return {zero: Fraction(1)}
        if j > R:
            return {}
        m = [0] * R
        m[j - 1] = 1
        return {tuple(m): Fraction(1)}

    ps = {}
    for j in range(1, R + 1):
        acc = scal(e(j), Fraction((-1) ** (j - 1) * j))
        for i in range(1, j):
            acc = add(acc, scal(mul(e(i), ps[j - i]), Fraction((-1) ** (i - 1))))
        ps[j] = acc

    def p_(j):
        return ps[j] if j <= R else {}

    Ps = {}
    for j in range(1, R + 1):
        acc = {}
        for i in range(0, j + 1):
            J = j + i * (p - 1)
            if J > R:
                break
            acc = add(acc, scal(p_(J), Fraction(comb(j, i))))
        Ps[j] = acc
    Es = {0: {zero: Fraction(1)}}
    for k in range(1, R + 1):
        acc = {}
        for i in range(1, k + 1):
            acc = add(acc, scal(mul(Es[k - i], Ps[i]), Fraction((-1) ** (i - 1))))
        Es[k] = scal(acc, Fraction(1, k))
    outs = {}
    for k in range(0, R + 1):
        out = {}
        for kk, v in Es[k].items():
            assert v.denominator == 1, ("non-integral E coefficient", k, kk, v)
            c = int(v) % p
            if c:
                out[kk] = c
        outs[k] = out
    return outs


# ---------------------------------------------------------------- the checks

def check(n, p, d, verbose=True):
    l = len(d)
    m = sum(d)
    r = n + 1 + m
    Rg = Poly(p, d)
    fails = []

    # gamma(V) = prod (1+h_i)^{d_i}
    gV = Rg.one()
    for i, di in enumerate(d):
        gV = Rg.mul(gV, Rg.pow(Rg.add(Rg.one(), Rg.gen(i)), di))
    cV = {a: Rg.part(gV, a) for a in range(0, m + 1)}

    # ---- L1
    gV2 = Rg.one()
    for i, di in enumerate(d):
        assert di % p == 0, "L1 needs p | d_i"
        gV2 = Rg.mul(gV2, Rg.pow(Rg.add(Rg.one(), Rg.gen(i, p)), di // p))
    if gV != gV2:
        fails.append("L1")

    # ---- L2
    PgV = Rg.steenrod_total(gV)
    gV3 = Rg.one()
    for i, di in enumerate(d):
        f = Rg.add(Rg.add(Rg.one(), Rg.gen(i, p)), Rg.gen(i, p * p))
        gV3 = Rg.mul(gV3, Rg.pow(f, di // p))
    if PgV != gV3:
        fails.append("L2")

    # ---- L3a
    for a in range(0, m + 1):
        if a % p and cV[a]:
            fails.append(f"L3a(a={a})")

    # ---- L3b
    for a in range(0, m + 1):
        if not cV[a]:
            continue
        for i in range(0, r + 2):
            Pi = Rg.steenrod_i(cV[a], i)
            if i % p and Pi:
                fails.append(f"L3b(a={a},i={i})")

    # ---- L0 and L4a
    Es = phi_universal(r, p)
    for a in range(1, r + 1):
        # E_a(gamma(V)) evaluated
        val = {}
        for exps, c in Es[a].items():
            term = Rg.scal(Rg.one(), c)
            for j, ee in enumerate(exps):
                if ee:
                    term = Rg.mul(term, Rg.pow(cV.get(j + 1, {}), ee))
            val = Rg.add(val, term)
        want = Rg.steenrod_total(cV.get(a, {}))
        if val != want:
            fails.append(f"L0(a={a})")
        # L4a: the linear part of E_a
        lin = {}
        for exps, c in Es[a].items():
            if sum(exps) == 1:
                jj = exps.index(1) + 1
                lin[jj] = c % p
        pred = {}
        i = 0
        while a + i * (p - 1) <= r:
            c = ((-1) ** (i * (p - 1)) * comb(a - 1, i)) % p
            if c:
                pred[a + i * (p - 1)] = c
            i += 1
        if lin != pred:
            fails.append(f"L4a(a={a}): exact {lin} vs predicted {pred}")

    # ---- L4 / L5 / L6 / L7 : work with symbolic b
    # unknowns: b_nu for monomials nu; represent an element of A with affine coefficients
    monos = [tuple(a) for a in product(*[range(di + 1) for di in d])]
    idx = {mo: i for i, mo in enumerate(monos)}
    nv = len(monos)

    def aff_zero():
        return {}

    def aff_add(a, b, s=1):
        out = {k: v[:] for k, v in a.items()}
        for k, v in b.items():
            w = out.setdefault(k, [0] * nv)
            for i in range(nv):
                w[i] = (w[i] + s * v[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    def aff_mul_const(c, a):
        """c a plain poly, a affine"""
        out = {}
        for m1, v1 in c.items():
            for m2, v2 in a.items():
                k = tuple(x + y for x, y in zip(m1, m2))
                if any(k[i] > d[i] for i in range(l)):
                    continue
                w = out.setdefault(k, [0] * nv)
                for i in range(nv):
                    if v2[i]:
                        w[i] = (w[i] + v1 * v2[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    bsym = {}
    for mo in monos:
        v = [0] * nv
        v[idx[mo]] = 1
        bsym[mo] = v
    bpart = {k: {mo: v for mo, v in bsym.items() if sum(mo) == k} for k in range(0, m + 1)}
    B = aff_mul_const(gV, bsym)
    Bpart = {k: {mo: v for mo, v in B.items() if sum(mo) == k} for k in range(0, m + 1)}

    def aff_steenrod_i(a, i):
        """P^i on affine homogeneous a."""
        if not a:
            return {}
        w = sum(next(iter(a)))
        out = {}
        for mo, v in a.items():
            terms = [(tuple([0] * l), 1)]
            for ii in range(l):
                new = []
                for mm, c in terms:
                    for j in range(mo[ii] + 1):
                        cc = comb(mo[ii], j) % p
                        if not cc:
                            continue
                        e = list(mm)
                        e[ii] = mo[ii] + j * (p - 1)
                        if e[ii] > d[ii]:
                            continue
                        new.append((tuple(e), (c * cc) % p))
                terms = new
            for mm, c in terms:
                if sum(mm) != w + i * (p - 1):
                    continue
                ww = out.setdefault(mm, [0] * nv)
                for ii in range(nv):
                    if v[ii]:
                        ww[ii] = (ww[ii] + c * v[ii]) % p
        return {k: v for k, v in out.items() if any(v)}

    def wu_row(j, i):
        """the weight-(j-n-1+i(p-1)) component of  P(B_{j-n-1}) - RHS_j,  as an affine elt."""
        k = j - n - 1
        lhs = aff_steenrod_i(Bpart.get(k, {}), i) if 0 <= k <= m else {}
        rhs = {}
        for a in range(0, min(j, m) + 1):
            bp = j - a
            if bp < 1:
                continue
            if not cV.get(a):
                continue
            for i2 in range(0, i + 1):
                ip = i - i2                      # power applied to gamma_a(V) is i2
                Pa = Rg.steenrod_i(cV[a], i2)
                if not Pa:
                    continue
                c = ((-1) ** (ip * (p - 1)) * comb(bp - 1, ip)) % p
                if not c:
                    continue
                kk = bp - n - 1 + ip * (p - 1)
                if kk < 0 or kk > m:
                    continue
                term = aff_mul_const(Rg.scal(Pa, c), bpart.get(kk, {}))
                rhs = aff_add(rhs, term)
        return aff_add(lhs, rhs, -1)

    # ---- L4: my rows must span the same space as tools/lix_modp_fast.py's rows
    myrows = []
    for j in range(1, r + 1):
        for i in range(0, r + 2):
            w = j - n - 1 + i * (p - 1)
            if w < 0 or w > m:
                continue
            row = wu_row(j, i)
            for mo, v in row.items():
                if any(v):
                    myrows.append(v[:])
    fastrows = fast_rows(n, p, d)

    def rank(M):
        M = [x[:] for x in M]
        rk = 0
        cols = len(M[0]) if M else 0
        for c in range(cols):
            piv = next((t for t in range(rk, len(M)) if M[t][c] % p), None)
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            inv = pow(M[rk][c], p - 2, p)
            M[rk] = [(x * inv) % p for x in M[rk]]
            for t in range(len(M)):
                if t != rk and M[t][c] % p:
                    f = M[t][c]
                    M[t] = [(x - f * y) % p for x, y in zip(M[t], M[rk])]
            rk += 1
        return rk

    ra, rb, rab = rank(myrows), rank(fastrows), rank(myrows + fastrows)
    if not (ra == rb == rab):
        fails.append(f"L4(row spaces differ: mine {ra}, fast {rb}, joint {rab})")

    # ---- L5: the diagonal relation
    diag_ok = True
    for i in range(1, (m + n) // p + 1):
        k = i * p - n
        if k < 0 or k > m:
            continue
        j = i + 1
        # instability: weight of B_{j-n-1} = i-n < i
        if not (i - n < i):
            fails.append(f"L5(instability fails at i={i})")
        row = wu_row(j, i)
        for mo, v in row.items():
            if sum(mo) != k:
                fails.append(f"L5(off-weight row at i={i})")
            # the row is (lhs - rhs) and the leading term sits in rhs, so the
            # coefficient of b_mo must be exactly -1 (= p-1) mod p
            if v[idx[mo]] % p != (p - 1) % p:
                fails.append(f"L5(leading coeff {v[idx[mo]]} != -1 at i={i}, mo={mo})")
                diag_ok = False
            for nu_i, c in enumerate(v):
                if not c % p:
                    continue
                nu = monos[nu_i]
                if nu == mo:
                    continue
                if sum(nu) >= k or (sum(nu) - k) % p:
                    fails.append(f"L5(bad support {nu} for k={k} at i={i})")
                    diag_ok = False

    # ---- L6: run the induction
    zeroed = set()
    for i in range(0, (m + n) // p + 1):
        k = i * p - n
        if k < 0 or k > m:
            continue
        j = i + 1
        row = wu_row(j, i)
        for mo, v in row.items():
            rem = [nu_i for nu_i, c in enumerate(v) if c % p and nu_i not in zeroed]
            if rem != [idx[mo]]:
                fails.append(f"L6(step k={k}, mo={mo} not triangular: {len(rem)} live)")
            zeroed.add(idx[mo])
    want = {idx[mo] for mo in monos if sum(mo) % p == 0}
    if not want <= zeroed:
        fails.append(f"L6(missed {len(want - zeroed)} of the residue-0 unknowns)")

    # ---- L7: the target
    top = tuple(d)
    L = B.get(top, [0] * nv)
    if not any(L):
        fails.append("L7(target functional is identically zero -- degenerate case)")
    for nu_i, c in enumerate(L):
        if c % p and nu_i not in zeroed:
            fails.append(f"L7(target uses live unknown {monos[nu_i]})")

    status = "ALL LEMMAS OK" if not fails else "FAILS: " + "; ".join(sorted(set(fails))[:6])
    if verbose:
        print(f"n={n} p={p} d={list(d)}  m={m} r={r} unknowns={nv}: {status}", flush=True)
    return fails


def fast_rows(n, p, d):
    """the constraint rows of tools/lix_modp_fast.py, verbatim logic."""
    monos = [tuple(a) for a in product(*[range(di + 1) for di in d])]
    idx = {mo: i for i, mo in enumerate(monos)}
    nv = len(monos)
    l = len(d)
    m = sum(d)
    r = n + 1 + m

    def part(a, k):
        return {mo: v for mo, v in a.items() if sum(mo) == k}

    def add(a, b, s=1):
        out = {k: v[:] for k, v in a.items()}
        for k, v in b.items():
            w = out.setdefault(k, [0] * (nv + 1))
            for i in range(nv + 1):
                w[i] = (w[i] + s * v[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    def mul_const_aff(a, b):
        out = {}
        for m1, v1 in a.items():
            c1 = v1[0]
            if not c1:
                continue
            for m2, v2 in b.items():
                k = tuple(x + y for x, y in zip(m1, m2))
                if any(k[i] > d[i] for i in range(l)):
                    continue
                w = out.setdefault(k, [0] * (nv + 1))
                for i in range(nv + 1):
                    if v2[i]:
                        w[i] = (w[i] + c1 * v2[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    def steen(a):
        out = {}
        for mo, v in a.items():
            terms = [(tuple([0] * l), 1)]
            for i in range(l):
                new = []
                for mm, c in terms:
                    for j in range(mo[i] + 1):
                        cc = comb(mo[i], j) % p
                        if not cc:
                            continue
                        e = list(mm)
                        e[i] = mo[i] + j * (p - 1)
                        if e[i] > d[i]:
                            continue
                        new.append((tuple(e), (c * cc) % p))
                terms = new
            for mm, c in terms:
                w = out.setdefault(mm, [0] * (nv + 1))
                for i in range(nv + 1):
                    if v[i]:
                        w[i] = (w[i] + c * v[i]) % p
        return {k: v for k, v in out.items() if any(v)}

    gV = {}
    for mo in monos:
        c = 1
        for i, di in enumerate(d):
            c = c * comb(di, mo[i])
        c %= p
        if c:
            gV[mo] = [c] + [0] * nv
    cV = {a: part(gV, a) for a in range(0, m + 1)}
    PcV = {a: steen(cV[a]) for a in range(0, m + 1)}
    bvec = {}
    for mo in monos:
        v = [0] * (nv + 1)
        v[1 + idx[mo]] = 1
        bvec[mo] = v
    bpart = {k: part(bvec, k) for k in range(0, m + 1)}
    bgV = mul_const_aff(gV, bvec)

    def cdelta(k):
        kk = k - n - 1
        return bpart.get(kk, {}) if kk >= 0 else {}

    def coeff(b, i):
        return ((-1) ** (i * (p - 1)) * (comb(b, i) + (p - 1) * comb(b - 1, i - 1))) % p

    rows = []
    for j in range(1, r + 1):
        lhs = steen(part(bgV, j - n - 1)) if j - n - 1 >= 0 else {}
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
                    inner = add(inner, cdelta(b + i * (p - 1)), c)
                i += 1
            if inner:
                rhs = add(rhs, mul_const_aff(PcV[a], inner))
        diff = add(lhs, rhs, -1)
        for mo, v in diff.items():
            assert v[0] == 0
            row = v[1:]
            if any(row):
                rows.append(row)
    return rows


if __name__ == "__main__":
    cases = [
        (2, 2, [2]), (2, 2, [4]), (2, 2, [2, 4]), (2, 2, [2, 4, 8]),
        (3, 3, [3]), (3, 3, [6]), (3, 3, [3, 6]), (3, 3, [3, 6, 12]),
        (4, 2, [4]), (4, 2, [4, 8]), (4, 2, [8]),
        (5, 5, [5]), (5, 5, [5, 10]),
        (6, 2, [6]), (6, 2, [12]), (6, 2, [6, 12]), (6, 2, [6, 12, 24]),
        (6, 3, [6]), (6, 3, [12]), (6, 3, [6, 12]), (6, 3, [6, 12, 24]),
        (7, 7, [7]), (7, 7, [7, 14]),
        (10, 2, [10, 20]), (10, 5, [10, 20]),
        (11, 11, [11]),
        (12, 2, [12, 24]), (12, 3, [12, 24]),
    ]
    if len(sys.argv) > 1:
        cases = [eval(a) for a in sys.argv[1:]]
    nbad = 0
    for (n, p, d) in cases:
        try:
            f = check(n, p, d)
        except Exception as ex:
            print(f"n={n} p={p} d={d}: EXC {type(ex).__name__}: {ex}", flush=True)
            nbad += 1
            continue
        if f:
            nbad += 1
    print()
    print("cases with any lemma failure:", nbad, "of", len(cases))
