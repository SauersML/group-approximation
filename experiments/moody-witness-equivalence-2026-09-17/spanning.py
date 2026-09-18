#!/usr/bin/env python3
"""Exact rank certificates for the spanning lemmas behind
`moody-witness-exists-iff-outside-burau-kernel`.

Setting (artifact research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md,
Sections 2-4).  For g in B_{n+1} the lifted action on H = Z[t^{+-1}]^{n+1} has matrix J(g)
(rows act: g_*(e_j) = sum_k J[j][k] e_k), and J(g) is rho_{n+1}(w') possibly with t -> 1/t,
w' in {w, rev w, mirror w, rev mirror w}.  The loop class of beta_*^3 is r = e_3 (a row),
and the intersection form with alpha is a column c = eps (1, -t^{+-1}, 0, ..., 0)^T, so that
(1 - t^s) M_g = r J(g) c   (artifact Lemma 3.1 plus Section 4.2; moody_gamma_trivial.py).

As sets, {J(g) : g in a subgroup S} is one of
  G_rho(S)  = rho(S)                      (variants w, mirror w; mirror(S) = S for S = f(B_n), K_{n+1})
  G_rev(S)  = D^{-1} rho(S)^T D           (variants rev w, rev mirror w)
possibly with t -> 1/t.  Orbit spans of a finitely generated matrix group are closures under
the generator matrices (Cayley-Hamilton gives the inverses).

The witness difference is, in the two composition orders,
  order 1: r (J(Psi) - I) J(Gamma) c,     order 2: r J(Gamma) (J(Psi) - I) c,
with Psi = f(y Phi y^{-1}).  The argument of the claim needs, in each variant:
  (a) span{ J(Gamma) c : Gamma in K_{n+1} } + Fix_col(f(B_n))            = Q(t)^{n+1}
  (b) span{ r J(y)     : y in f(B_n) }       + Fix_row(f(B_n))            = Q(t)^{n+1}
  (c) span{ r J(Gamma) : Gamma in K_{n+1} } + Fix_row(f(B_n))            = Q(t)^{n+1}
  (d) span{ J(y) c     : y in f(B_n) }       + Fix_col(f(B_n))            = Q(t)^{n+1}
Here Fix_col(S) = common fixed columns of J(S), Fix_row(S) = common fixed rows.  These kill
J(Psi) - I on the right resp. left.  (a)+(b) serve order 1, (c)+(d) serve order 2.

Ranks are computed exactly over Q after specialising t to a rational t0.  Specialisation can
only lower rank, so full rank at one t0 certifies full rank over Q(t).  (Fixed vectors are
computed at t0 too; a fixed vector over Q(t) specialises to a fixed vector at t0, but the
converse fails, so we instead use the explicit Q(t)-fixed vectors e_{n+1} and the all-ones /
(1, t, ..., t^n) vectors and check they are fixed; see fixed_vectors().)
"""
import sys
from fractions import Fraction as Fr


def ident(m):
    return [[Fr(int(i == j)) for j in range(m)] for i in range(m)]


def mmul(A, B):
    m = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(m)] for i in range(m)]


def mvec(A, v):
    return [sum(A[i][k] * v[k] for k in range(len(v))) for i in range(len(A))]


def vmat(v, A):
    return [sum(v[k] * A[k][j] for k in range(len(v))) for j in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def gen(m, s, t):
    i = abs(s) - 1
    M = ident(m)
    if s > 0:
        blk = [[1 - t, t], [Fr(1), Fr(0)]]
    else:
        blk = [[Fr(0), Fr(1)], [1 / t, 1 - 1 / t]]
    for a in range(2):
        for b in range(2):
            M[i + a][i + b] = blk[a][b]
    return M


def rho(m, word, t):
    M = ident(m)
    for s in word:
        M = mmul(M, gen(m, s, t))
    return M


def inv(w):
    return [-s for s in reversed(w)]


def Aw(i, j):
    c = list(range(j - 1, i, -1))
    return c + [i, i] + inv(c)


def rank(vecs):
    rows = [list(v) for v in vecs]
    if not rows:
        return 0
    m = len(rows[0])
    r = 0
    for col in range(m):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][col] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col] / rows[r][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def orbit_span(start, gens, side):
    basis = [list(start)]
    queue = [list(start)]
    while queue:
        v = queue.pop()
        for G in gens:
            w = mvec(G, v) if side == "col" else vmat(v, G)
            if rank(basis + [w]) > len(basis):
                basis.append(w)
                queue.append(w)
    return basis


def variant(M, kind, t, m):
    if kind == "rho":
        return M
    D = [[t ** i if i == j else Fr(0) for j in range(m)] for i in range(m)]
    Di = [[t ** (-i) if i == j else Fr(0) for j in range(m)] for i in range(m)]
    return mmul(mmul(Di, transpose(M)), D)


def fixed_vectors(gens, m, t):
    """Candidate Q(t)-fixed vectors, kept only if fixed by every generator at t0.
    The candidates are fixed over Q(t) by hand: each 2x2 Burau block [[1-t, t],[1, 0]] has row
    sums 1 (so the all-ones column is fixed) and (1, t) [[1-t, t],[1, 0]] = (1, t) (so the row
    (1, t, ..., t^{m-1}) is fixed); generators of f(B_n) touch only coordinates 1..n, so e_m is
    fixed on both sides.  In the rev variant D^{-1} M^T D the roles of these vectors are
    exchanged (ones column <-> powers row), and e_m stays fixed.  The code only selects which of
    these hand-proved fixed vectors apply to the variant at hand."""
    e_last = [Fr(int(i == m - 1)) for i in range(m)]
    ones = [Fr(1)] * m
    powers = [t ** i for i in range(m)]
    cands = [e_last, ones, powers]
    cols = [v for v in cands if all(mvec(G, v) == v for G in gens)]
    rows = [v for v in cands if all(vmat(v, G) == v for G in gens)]
    return cols, rows


def check(n, t, kind, v):
    m = n + 1
    K = [variant(rho(m, Aw(j, m), t), kind, t, m) for j in range(1, m)]
    Bn = [variant(gen(m, i, t), kind, t, m) for i in range(1, n)]
    fcols, frows = fixed_vectors(Bn, m, t)
    r = [Fr(int(i == 2)) for i in range(m)]
    c = [Fr(0)] * m
    c[0], c[1] = Fr(1), v
    ra = rank(orbit_span(c, K, "col") + fcols)
    rb = rank(orbit_span(r, Bn, "row") + frows)
    rc = rank(orbit_span(r, K, "row") + frows)
    rd = rank(orbit_span(c, Bn, "col") + fcols)
    return (ra, rb, rc, rd), len(fcols), len(frows)


def main():
    ns = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    allok = True
    for n in ns:
        m = n + 1
        okn = True
        for t in (Fr(2), Fr(1, 2), Fr(3), Fr(-5, 7)):
            for kind in ("rho", "rev"):
                for sgn in (1, -1):
                    for e in (-2, -1, 0, 1, 2):
                        v = sgn * t ** e
                        ranks, nfc, nfr = check(n, t, kind, v)
                        ok = all(x == m for x in ranks)
                        okn &= ok
                        if not ok:
                            print("n", n, "t0", t, kind, "v", v, "ranks", ranks,
                                  "fixed cols/rows", nfc, nfr)
        print("n =", n, ": (a)-(d) full rank", m, "in all 80 variants:", okn)
        allok &= okn
    print("ALL SPANNING CHECKS PASS:", allok)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
