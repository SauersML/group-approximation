#!/usr/bin/env python3
"""Checks for slit-origami-z2-pair-has-rank-distance-half-l.

Model (L >= 2, s = L // 2).  Squares are (i, x, y) with i in {0,1} and x, y in Z/L.
  sigma(i,x,y) = (i, x+1, y)
  tau(i,x,y)   = (1-i, x, 1)  if y == 0 and 0 <= x < s   (slit crossing)
               = (i, x, y+1)  otherwise
b, c are the permutation matrices of sigma, tau on C^(2 L^2).

C0  rank(bc - cb) = 2 (exact rank over Q).
C1  the rectangle word W = c^-s b^-s c^s b^s (b^s applied first) returns every square to its own
    base square and swaps the sheet on exactly 2 s^2 base squares, so rank(W(b,c) - I) = 2 s^2.
    Together with rank(W(b,c) - W(b',c')) <= 2s rank(b'-b) + 2s rank(c'-c) and W(b',c') = I for a
    commuting pair, this gives rank(b'-b) + rank(c'-c) >= s.
C2  the unslit shift c'(i,x,y) = (i,x,y+1) commutes with b and rank(c - c') = s exactly.
C3  the base-square count 2 a h of C1 for general rectangles a x h with 1 <= a <= s, 1 <= h <= L-1.

Run: nice -n 10 timeout 1200 python3 check_rank_distance.py
"""
from fractions import Fraction


def perms(L):
    s = L // 2
    n = 2 * L * L
    idx = lambda i, x, y: (i * L + (x % L)) * L + (y % L)
    sig = [0] * n
    tau = [0] * n
    for i in range(2):
        for x in range(L):
            for y in range(L):
                sig[idx(i, x, y)] = idx(i, x + 1, y)
                tau[idx(i, x, y)] = idx(1 - i, x, 1) if (y == 0 and 0 <= x < s) else idx(i, x, y + 1)
    return s, n, idx, sig, tau


def exact_rank(rows):
    M = [[Fraction(v) for v in row] for row in rows]
    rank, ncols = 0, (len(M[0]) if M else 0)
    for col in range(ncols):
        piv = next((i for i in range(rank, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        for i in range(len(M)):
            if i != rank and M[i][col] != 0:
                f = M[i][col] / M[rank][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rank])]
        rank += 1
    return rank


def diff_rank(P, Q, n):
    """exact rank of (perm matrix P) - (perm matrix Q)."""
    cols = [q for q in range(n) if P[q] != Q[q]]
    if not cols:
        return 0
    rows = sorted({P[q] for q in cols} | {Q[q] for q in cols})
    pos = {r: k for k, r in enumerate(rows)}
    mat = [[0] * len(cols) for _ in rows]
    for j, q in enumerate(cols):
        mat[pos[P[q]]][j] += 1
        mat[pos[Q[q]]][j] -= 1
    return exact_rank(mat)


def swapped_count(L, a, h, sig, tau, n):
    inv_sig = [0] * n
    inv_tau = [0] * n
    for q in range(n):
        inv_sig[sig[q]] = q
        inv_tau[tau[q]] = q
    ops = [sig] * a + [tau] * h + [inv_sig] * a + [inv_tau] * h
    swapped = 0
    for q in range(n):
        p = q
        for op in ops:
            p = op[p]
        assert p // L % L == q // L % L and p % L == q % L, ("returns to base square", L, a, h)
        if p != q:
            swapped += 1
    assert swapped % 2 == 0
    return swapped // 2   # base squares; W is a product of this many disjoint transpositions


def main():
    print("C0-C2: rank(bc-cb)=2, rank(W_rect - I) = 2 s^2, unslit c' commutes with rank(c-c') = s")
    for L in list(range(2, 41)) + [64]:
        s, n, idx, sig, tau = perms(L)
        bc = [sig[tau[q]] for q in range(n)]
        cb = [tau[sig[q]] for q in range(n)]
        r0 = diff_rank(bc, cb, n)
        assert r0 == 2, ("C0", L, r0)
        sw = swapped_count(L, s, s, sig, tau, n)
        assert sw == 2 * s * s, ("C1", L, sw)
        cp = [idx(q // (L * L), q // L % L, q % L + 1) for q in range(n)]
        assert all(sig[cp[q]] == cp[sig[q]] for q in range(n)), "C2 commute"
        rk = diff_rank(tau, cp, n)
        assert rk == s, ("C2 rank", L, rk)
        if L <= 8 or L in (40, 64):
            print(f"  L={L:3d} n={n:5d} s={s:3d}  rank(bc-cb)={r0}  rank(W-I)={sw:5d}=2s^2  rank(c-c')={rk}=s  "
                  f"=> min rank(b'-b)+rank(c'-c) = {s}: OK")
    print("  all L in 2..40, 64: OK")
    print("C3: rectangle counts 2ah for 1<=a<=s, 1<=h<=L-1")
    for L in range(2, 13):
        s, n, idx, sig, tau = perms(L)
        for a in range(1, s + 1):
            for h in range(1, L):
                assert swapped_count(L, a, h, sig, tau, n) == 2 * a * h, ("C3", L, a, h)
    print("  all L in 2..12: OK")


if __name__ == "__main__":
    main()
