#!/usr/bin/env python3
"""Exact sanity test of the covariant tower construction of Theorem A
(research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md, sections 2-5).

Toy SFT Omega_S = Omega_T on letters a = (wc, hc, t) in {0,1}^3:
  a vertical domino is legal iff both letters have the same wc,
  a horizontal domino is legal iff both letters have the same hc.
For this SFT every rectangular pattern whose dominoes are legal extends to a point.
Shapes: w(a) = 2 + wc, h(a) = 2 + hc (letter-dependent, all >= 2).
omega(a)_(i,j) = (WC[wc][i], HC[hc][j], tau(a,i,j)).

Parent: a noncommutative covariant 1-family on the torus Z/6 x Z/3 with fibre F_p^2.
The script builds the tower space, A_1, A_2, B_1, B_2 and E_b(0) exactly as in section 3-4
and checks over F_p (p = 1000003):
  Lemma 1, Lemma 2, (Q1), (Q2) at scale 2, domino (Q3) at scale 2,
  Proposition 5 against an independent classical layout of omega(rho),
  the dimension formula, and noncommutativity of the child family.
A negative control with widths not column-constant must fail.
Arithmetic: float64 matrices with entries in [0,p), reduced mod p after every product
(sums < 324 p^2 < 2^53, so all results are exact).
"""
import itertools
import sys
import numpy as np

P = 1000003
N1, N2 = 6, 3
DV = 2
LET = [(wc, hc, t) for wc in (0, 1) for hc in (0, 1) for t in (0, 1)]
NL = len(LET)
WC = {0: (0, 1), 1: (1, 0, 1)}
HC = {0: (1, 0), 1: (0, 1, 1)}
WCPAR = [0, 1, 1, 0, 1, 0]
HCPAR = [0, 1, 1]
Q1MAP = {(0, 0): 'e', (3, 1): 'f', (1, 2): 'one', (4, 0): 'one'}
MATS = {'e': np.array([[1., 0.], [0., 0.]]), 'f': np.array([[1., 1.], [0., 0.]]),
        'one': np.eye(2), 'zero': np.zeros((2, 2))}


def mm(a, b):
    return np.mod(a @ b, P)


def md(a):
    return np.mod(a, P)


def iszero(a):
    return not np.any(np.mod(a, P))


def eq(a, b):
    return iszero(a - b)


def idx(wc, hc, t):
    return LET.index((wc, hc, t))


def make_variant(bad):
    if not bad:
        w = [2 + a[0] for a in LET]
        h = [2 + a[1] for a in LET]

        def om(a, i, j):
            wc, hc, t = LET[a]
            return idx(WC[wc][i], HC[hc][j], (t + i * (j + 1) + wc * j) % 2)
    else:  # negative control: width depends on t, so (M1) fails on legal words
        w = [2 + a[2] for a in LET]
        h = [2 + a[1] for a in LET]

        def om(a, i, j):
            wc, hc, t = LET[a]
            return idx((i + wc) % 2, HC[hc][j], (t + i + j) % 2)
    return w, h, om


def site(c1, c2):
    return (c1 % N1) * N2 + (c2 % N2)


DW = N1 * N2 * DV


def p_letter(a, c1, c2):
    wc, hc, t = LET[a]
    if wc != WCPAR[c1 % N1] or hc != HCPAR[c2 % N2]:
        return MATS['zero']
    q1 = MATS[Q1MAP.get((c1 % N1, c2 % N2), 'zero')]
    return q1 if t == 1 else np.eye(2) - q1


def Eprime(a, z):
    """E'_a(z) acts on the fibre of site c as p_a(c - z)."""
    M = np.zeros((DW, DW))
    for c1 in range(N1):
        for c2 in range(N2):
            s = site(c1, c2)
            M[DV * s:DV * s + DV, DV * s:DV * s + DV] = p_letter(a, c1 - z[0], c2 - z[1])
    return md(M)


def shift(e):
    U = np.zeros((DW, DW))
    for c1 in range(N1):
        for c2 in range(N2):
            for v in range(DV):
                U[DV * site(c1 + e[0], c2 + e[1]) + v, DV * site(c1, c2) + v] = 1.
    return U


LOG = []


def out(s):
    LOG.append(s)
    print(s)


def check(name, cond, must=True):
    out(f"  [{'ok' if cond else 'FAIL'}] {name}")
    if must and not cond:
        print("ASSERTION FAILED:", name)
        sys.exit(1)
    return cond


def legal_pattern(sig, m, n):  # sig: dict (c1,c2)->letter on [0,m)x[0,n)
    for c1 in range(m):
        for c2 in range(n):
            if c2 + 1 < n and LET[sig[(c1, c2)]][0] != LET[sig[(c1, c2 + 1)]][0]:
                return False
            if c1 + 1 < m and LET[sig[(c1, c2)]][1] != LET[sig[(c1 + 1, c2)]][1]:
                return False
    return True


def layout(sig, m, n, w, h, om):
    """Classical block layout of omega(rho) for a legal rho on [0,m)x[0,n) (M2)."""
    X = [0]
    for c1 in range(m):
        X.append(X[-1] + w[sig[(c1, 0)]])
    Y = [0]
    for c2 in range(n):
        Y.append(Y[-1] + h[sig[(0, c2)]])
    img = {}
    for c1 in range(m):
        for c2 in range(n):
            a = sig[(c1, c2)]
            assert w[a] == X[c1 + 1] - X[c1] and h[a] == Y[c2 + 1] - Y[c2]
            for i in range(w[a]):
                for j in range(h[a]):
                    img[(X[c1] + i, Y[c2] + j)] = om(a, i, j)
    return img, X[-1], Y[-1]


def run(bad):
    out(f"== variant: {'NEGATIVE CONTROL (widths depend on t)' if bad else 'toy SFT, shapes 2 + wc by 2 + hc'}")
    w, h, om = make_variant(bad)
    wmax, hmax = max(w), max(h)
    U1, U2 = shift((1, 0)), shift((0, 1))
    U1i, U2i = U1.T.copy(), U2.T.copy()
    E0 = [Eprime(a, (0, 0)) for a in range(NL)]
    I = np.eye(DW)
    ok = True
    # ---- parent family
    check("parent covariance E'_a(e_l) = u_l E'_a(0) u_l^-1",
          all(eq(Eprime(a, (1, 0)), mm(mm(U1, E0[a]), U1i)) and eq(Eprime(a, (0, 1)), mm(mm(U2, E0[a]), U2i))
              for a in range(NL)))
    check("parent (Q1)", eq(sum(E0), I) and all(eq(mm(E0[a], E0[b]), E0[a] if a == b else 0 * I)
                                                  for a in range(NL) for b in range(NL)))
    check("parent (Q2) at scale 1",
          all(iszero(mm(E0[a], Eb) - mm(Eb, E0[a]))
              for z in itertools.product(range(-2, 3), repeat=2) for b in range(NL)
              for Eb in [Eprime(b, z)] for a in range(NL)))
    check("parent (Q3) dominoes",
          all(iszero(mm(E0[a], Eprime(b, (0, 1)))) for a in range(NL) for b in range(NL) if LET[a][0] != LET[b][0])
          and all(iszero(mm(E0[a], Eprime(b, (1, 0)))) for a in range(NL) for b in range(NL) if LET[a][1] != LET[b][1]))
    X0 = sum(E0[a] for a in range(NL) if LET[a][2] == 1)
    X31 = sum(Eprime(a, (3, 1)) for a in range(NL) if LET[a][2] == 1)
    check("parent is noncommutative: [E'_(t=1)(0), E'_(t=1)(3,1)] != 0", not iszero(mm(X0, X31) - mm(X31, X0)))
    if not bad:
        n_leg = 0
        for cls in itertools.product((0, 1), repeat=6):
            for ts in itertools.product((0, 1), repeat=9):
                sig = {(c1, c2): idx(cls[c1], cls[3 + c2], ts[3 * c1 + c2]) for c1 in range(3) for c2 in range(3)}
                assert legal_pattern(sig, 3, 3)
                img, W, H = layout(sig, 3, 3, w, h, om)
                assert legal_pattern(img, W, H)
                n_leg += 1
        check(f"omega maps all {n_leg} legal 3x3 patterns to legal patterns (H1 on 3x3 words)", True)
    # ---- Lemma 1
    Meq = {m: sum((E0[a] for a in range(NL) if w[a] == m), 0 * I) for m in range(1, wmax + 1)}
    Neq = {n: sum((E0[a] for a in range(NL) if h[a] == n), 0 * I) for n in range(1, hmax + 1)}
    Mgt = {i: sum((Meq[m] for m in Meq if m > i), 0 * I) for i in range(0, wmax + 1)}
    Ngt = {j: sum((Neq[n] for n in Neq if n > j), 0 * I) for j in range(0, hmax + 1)}
    lem1 = all(eq(mm(U2, Meq[m]), mm(Meq[m], U2)) for m in Meq) and all(eq(mm(U1, Neq[n]), mm(Neq[n], U1)) for n in Neq)
    ok &= check("Lemma 1: u_2 commutes with M_(=m)(0), u_1 with N_(=n)(0)", lem1, must=not bad)
    # ---- tower space
    nb = wmax * hmax
    DT = nb * DW

    def blk(i, j):
        return (i * hmax + j) * DW

    def put(M, ti, tj, si, sj, X):
        M[blk(ti, tj):blk(ti, tj) + DW, blk(si, sj):blk(si, sj) + DW] += X

    Pi = np.zeros((DT, DT))
    for i in range(wmax):
        for j in range(hmax):
            put(Pi, i, j, i, j, mm(Mgt[i], Ngt[j]))
    B1 = np.zeros((DT, DT)); A1 = np.zeros((DT, DT)); B2 = np.zeros((DT, DT)); A2 = np.zeros((DT, DT))
    for i in range(wmax):
        for j in range(hmax):
            if i + 1 < wmax:
                put(B1, i + 1, j, i, j, Mgt[i + 1])
                put(A1, i, j, i + 1, j, I)
            put(B1, 0, j, i, j, mm(U1i, Meq[i + 1]))
            put(A1, i, j, 0, j, mm(Meq[i + 1], U1))
            if j + 1 < hmax:
                put(B2, i, j + 1, i, j, Ngt[j + 1])
                put(A2, i, j, i, j + 1, I)
            put(B2, i, 0, i, j, mm(U2i, Neq[j + 1]))
            put(A2, i, j, i, 0, mm(Neq[j + 1], U2))
    B1, A1, B2, A2, Pi = md(B1), md(A1), md(B2), md(A2), md(Pi)
    check("Pi is idempotent", eq(mm(Pi, Pi), Pi))
    inv = all(eq(mm(Pi, mm(X, Pi)), mm(X, Pi)) for X in (A1, B1, A2, B2))
    ok &= check("Lemma 2: A_l, B_l map W_T into W_T", inv, must=not bad)
    L2b = (eq(mm(A1, mm(B1, Pi)), Pi) and eq(mm(B1, mm(A1, Pi)), Pi)
           and eq(mm(A2, mm(B2, Pi)), Pi) and eq(mm(B2, mm(A2, Pi)), Pi))
    ok &= check("Lemma 2: A_l B_l = B_l A_l = 1 on W_T", L2b, must=not bad)
    L2c = eq(mm(A1, mm(A2, Pi)), mm(A2, mm(A1, Pi)))
    ok &= check("Lemma 2: A_1 A_2 = A_2 A_1 on W_T", L2c, must=not bad)
    Eb0 = []
    for b in range(NL):
        M = np.zeros((DT, DT))
        for i in range(wmax):
            for j in range(hmax):
                put(M, i, j, i, j, sum((E0[a] for a in range(NL) if w[a] > i and h[a] > j and om(a, i, j) == b), 0 * I))
        Eb0.append(mm(md(M), Pi))
    q1 = eq(sum(Eb0), Pi) and all(eq(mm(Eb0[b], Eb0[c]), Eb0[b] if b == c else 0 * Pi) for b in range(NL) for c in range(NL))
    ok &= check("(Q1) for the child family", q1, must=not bad)
    if bad:
        out(f"  negative control: construction fails as expected = {not ok}")
        assert not ok
        return
    rank_formula = sum(w[a] * h[a] * int(round(np.trace(E0[a]))) % P for a in range(NL))
    check(f"dim W_T = trace(Pi) = {int(round(np.trace(Pi))) % P} = sum_a w h rank E'_a(0) = {rank_formula}",
          int(round(np.trace(Pi))) % P == rank_formula)
    out(f"  dim W' = {DW}, dim W_T = {rank_formula}")
    RMAX = 12
    pow1, pow2 = {0: Pi}, {0: Pi}  # pow_l[k] = A_l^k Pi (k >= 0), B_l^(-k) Pi (k < 0)
    for k in range(1, RMAX + 1):
        pow1[k], pow1[-k] = mm(A1, pow1[k - 1]), mm(B1, pow1[-k + 1])
        pow2[k], pow2[-k] = mm(A2, pow2[k - 1]), mm(B2, pow2[-k + 1])

    def Apow(z):  # A^z on W_T (times Pi), using invariance of W_T
        return mm(pow1[z[0]], pow2[z[1]])

    def G(Ezero, z, Az=None, Amz=None):
        Az = Apow(z) if Az is None else Az
        Amz = Apow((-z[0], -z[1])) if Amz is None else Amz
        return mm(mm(Az, Ezero), Amz)

    # ---- Proposition 5 against the classical layout
    Qsites = [(c1, c2) for c1 in range(3) for c2 in range(3)]
    fib_sigmas = {}
    for c1 in range(N1):
        for c2 in range(N2):
            choices = []
            for (d1, d2) in Qsites:
                wc, hc = WCPAR[(c1 - d1) % N1], HCPAR[(c2 - d2) % N2]
                typ = Q1MAP.get(((c1 - d1) % N1, (c2 - d2) % N2), 'zero')
                ts = {'zero': [0], 'one': [1]}.get(typ, [0, 1])
                choices.append([idx(wc, hc, t) for t in ts])
            lst = []
            for letters in itertools.product(*choices):
                sig = dict(zip(Qsites, letters))
                e = np.eye(2)
                for (d1, d2), a in sig.items():
                    e = mm(e, p_letter(a, c1 - d1, c2 - d2))
                if not iszero(e):
                    assert legal_pattern(sig, 3, 3)
                    lst.append((sig, e, layout(sig, 3, 3, w, h, om)[0]))
            fib_sigmas[(c1, c2)] = lst
    out(f"  surviving legal Q-patterns per fibre: {sorted(set(len(v) for v in fib_sigmas.values()))}")
    prop5 = True
    Box = [(z1, z2) for z1 in range(5) for z2 in range(5)]
    for z in Box:
        Az, Amz = Apow(z), Apow((-z[0], -z[1]))
        for b in range(NL):
            Gb = G(Eb0[b], z, Az, Amz)
            for i in range(wmax):
                for j in range(hmax):
                    for i2 in range(wmax):
                        for j2 in range(hmax):
                            blkm = Gb[blk(i, j):blk(i, j) + DW, blk(i2, j2):blk(i2, j2) + DW]
                            if (i, j) != (i2, j2):
                                prop5 &= iszero(blkm)
                                continue
                            ev = np.zeros((DW, DW))
                            for (c1, c2), lst in fib_sigmas.items():
                                s = site(c1, c2)
                                for sig, e, img in lst:
                                    a0 = sig[(0, 0)]
                                    if w[a0] > i and h[a0] > j and img[(i + z[0], j + z[1])] == b:
                                        ev[DV * s:DV * s + DV, DV * s:DV * s + DV] += e
                            prop5 &= eq(blkm, ev)
    check("Proposition 5: E_b(z) diagonal with entries ev_Q(f^b_(ij,z)) for all z in [0,4]^2, all b", prop5)
    # ---- (Q2) at scale 2 and domino (Q3) at scale 2
    q2 = True
    # [E_b(0), E_c(-z)] is conjugate by A^z to -[E_c(0), E_b(z)], so z >= 0 lexicographically suffices.
    for z in itertools.product(range(-4, 5), repeat=2):
        if z < (0, 0):
            continue
        Az, Amz = Apow(z), Apow((-z[0], -z[1]))
        Gz = [G(Eb0[c], z, Az, Amz) for c in range(NL)]
        for b in range(NL):
            for c in range(NL):
                q2 &= iszero(mm(Eb0[b], Gz[c]) - mm(Gz[c], Eb0[b]))
    check("(Q2) at scale 2: [E_b(0), E_c(z)] = 0 for all z in B_4 (lexicographically >= 0), all b, c", q2)
    Ge2 = [G(Eb0[c], (0, 1)) for c in range(NL)]
    Ge1 = [G(Eb0[c], (1, 0)) for c in range(NL)]
    q3 = (all(iszero(mm(Eb0[b], Ge2[c])) for b in range(NL) for c in range(NL) if LET[b][0] != LET[c][0])
          and all(iszero(mm(Eb0[b], Ge1[c])) for b in range(NL) for c in range(NL) if LET[b][1] != LET[c][1]))
    check("(Q3) at scale 2 via dominoes (sufficient for this SFT given (Q2))", q3)
    # ---- child noncommutativity
    Xt = sum(Eb0[b] for b in range(NL) if LET[b][2] == 1)
    found = None
    for r in range(5, 13):
        for z in itertools.product(range(-r, r + 1), repeat=2):
            if max(abs(z[0]), abs(z[1])) != r:
                continue
            Xz = G(Xt, z)
            if not iszero(mm(Xt, Xz) - mm(Xz, Xt)):
                found = z
                break
        if found:
            break
    check(f"child family is noncommutative: first [E_(t=1)(0), E_(t=1)(z)] != 0 at z = {found}", found is not None)


if __name__ == "__main__":
    run(bad=False)
    run(bad=True)
    out("ALL CHECKS PASSED")
