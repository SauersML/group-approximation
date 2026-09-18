#!/usr/bin/env python3
"""Checks for slit-origami-z2-pair-needs-logarithmic-rank-to-commute.

Model (L >= 2, s = L // 2).  Squares are (i, x, y) with i in {0,1} and x, y in Z/L.
  sigma(i,x,y) = (i, x+1, y)
  tau(i,x,y)   = (1-i, x, 1)  if y == 0 and 0 <= x < s   (slit crossing)
               = (i, x, y+1)  otherwise
b, c are the permutation matrices of sigma, tau on C^(2 L^2).

Part A (combinatorics, exact):
  A1 sigma, tau are permutations;
  A2 sigma tau != tau sigma on exactly 4 squares, and rank(bc - cb) = rank(b c b^-1 c^-1 - I) <= 4
     (exact rank over Q via fraction-free elimination on small L; numpy rank on larger L);
  A3 for every r = 1..floor(L/2) the ring word w_r (boundary of the 2r x 2r block of squares
     with columns s-r..s+r-1 and rows 1-r..r) has zero exponent sums in sigma and tau, has
     8r-4 letters, and its lift from sheet 0 ends on sheet 1 over the same base square;
  A4 the rings R_1, ..., R_floor(L/2) are pairwise disjoint.

Part B (sharpness in Hilbert--Schmidt, numerical):
  in the antisymmetric sector the pair is a signed torus shift with plaquette flux pi at the
  plaquettes (s-1, 0) and (L-1, 0).  A dipole stream function psi with Delta psi = pi (delta_p - delta_q)
  gives edge phases making an exactly commuting unitary pair (b', c'), equal to (b, c) on the
  symmetric sector.  We print ||b-b'||_HS^2 + ||c-c'||_HS^2, the commutator residual, and the
  proven lower bound ln(floor(L/2)+1)/64.

Run: nice -n 10 timeout 1200 python3 check_slit_origami.py
"""
import math
from fractions import Fraction

import numpy as np


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
                if y == 0 and 0 <= x < s:
                    tau[idx(i, x, y)] = idx(1 - i, x, 1)
                else:
                    tau[idx(i, x, y)] = idx(i, x, y + 1)
    return s, n, idx, sig, tau


def ring_word(L, s, r):
    """Letters ('b',+1/-1) or ('c',+1/-1) walking the boundary of the block
    columns s-r..s+r-1, rows 1-r..r, starting at the bottom-left square, counterclockwise."""
    w = []
    w += [("b", 1)] * (2 * r - 1)   # bottom row, left to right
    w += [("c", 1)] * (2 * r - 1)   # right column, bottom to top
    w += [("b", -1)] * (2 * r - 1)  # top row, right to left
    w += [("c", -1)] * (2 * r - 1)  # left column, top to bottom
    start = (s - r, 1 - r)
    return start, w


def exact_rank(rows):
    """Rank over Q of a list of integer row vectors (fraction-free Gaussian elimination)."""
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


def part_a(L):
    s, n, idx, sig, tau = perms(L)
    assert sorted(sig) == list(range(n)) and sorted(tau) == list(range(n)), "A1"
    bad = [q for q in range(n) if sig[tau[q]] != tau[sig[q]]]
    assert len(bad) == 4, ("A2 count", L, len(bad))
    # matrix of bc - cb restricted to its nonzero columns: column q has +1 at sigma(tau(q)), -1 at tau(sigma(q))
    rows_used = sorted({sig[tau[q]] for q in bad} | {tau[sig[q]] for q in bad})
    mat = [[0] * len(bad) for _ in rows_used]
    for j, q in enumerate(bad):
        mat[rows_used.index(sig[tau[q]])][j] += 1
        mat[rows_used.index(tau[sig[q]])][j] -= 1
    rk = exact_rank(mat)
    assert rk <= 4, "A2 rank"
    inv_sig = [0] * n
    inv_tau = [0] * n
    for q in range(n):
        inv_sig[sig[q]] = q
        inv_tau[tau[q]] = q
    act = {("b", 1): sig, ("b", -1): inv_sig, ("c", 1): tau, ("c", -1): inv_tau}
    rho = L // 2
    seen = set()
    for r in range(1, rho + 1):
        (x0, y0), w = ring_word(L, s, r)
        assert len(w) == 8 * r - 4, "A3 length"
        assert sum(e for (g, e) in w if g == "b") == 0 and sum(e for (g, e) in w if g == "c") == 0, "A3 exponents"
        q = idx(0, x0, y0)
        base_squares = [((x0) % L, (y0) % L)]
        for letter in w:   # the path; operator order is the reverse word, same path
            q = act[letter][q]
            base_squares.append((q // L % L, q % L))
        assert q == idx(1, x0, y0), ("A3 holonomy", L, r)
        ring = set(base_squares)
        assert len(ring) == 8 * r - 4, ("A3 ring size", L, r, len(ring))
        assert not (ring & seen), ("A4 disjoint", L, r)
        seen |= ring
    return s, rk


def part_b(L):
    s = L // 2
    rho = np.zeros((L, L))
    rho[(s - 1) % L, 0] += math.pi
    rho[(L - 1) % L, 0] -= math.pi
    kx = np.arange(L)
    lam = (2 * np.cos(2 * math.pi * kx / L) - 2)[:, None] + (2 * np.cos(2 * math.pi * kx / L) - 2)[None, :]
    rh = np.fft.fft2(rho)
    lam[0, 0] = 1.0
    ph = rh / lam
    ph[0, 0] = 0.0
    psi = np.real(np.fft.ifft2(ph))
    Ax = -(psi - np.roll(psi, 1, axis=1))  # A^x(x,y) = -(psi(x,y) - psi(x,y-1))
    Ay = psi - np.roll(psi, 1, axis=0)     # A^y(x,y) = psi(x,y) - psi(x-1,y)
    eps = np.ones((L, L))
    eps[0:s, 0] = -1.0
    # commutation check on the antisymmetric sector: phase of b'c' vs c'b' at (x,y) -> (x+1,y+1)
    bc = eps * np.exp(1j * (Ay + np.roll(Ax, -1, axis=1)))
    cb = np.roll(eps, -1, axis=0) * np.exp(1j * (Ax + np.roll(Ay, -1, axis=0)))
    resid = np.max(np.abs(bc - cb))
    hs2 = float(np.sum(np.abs(np.exp(1j * Ax) - 1) ** 2) + np.sum(np.abs(np.exp(1j * Ay) - 1) ** 2))
    return resid, hs2


def main():
    print("Part A: exact combinatorics")
    for L in list(range(2, 41)) + [64, 101]:
        s, rk = part_a(L)
        if L <= 12 or L in (40, 64, 101):
            print(f"  L={L:4d} s={s:3d} n={2*L*L:6d} |supp[sigma,tau]|=4 rank(bc-cb)={rk} rings 1..{L//2} swap sheets, disjoint: OK")
    print("  all L in 2..40, 64, 101: OK")
    print("Part B: dipole flat connection (HS upper bound) vs proven lower bound")
    print(f"  {'L':>5} {'n':>8} {'commutator residual':>20} {'HS^2 distance':>14} {'HS^2/ln L':>10} {'lower ln(L/2+1)/64':>19}")
    for L in [4, 8, 16, 32, 64, 128, 256, 512]:
        resid, hs2 = part_b(L)
        lb = math.log(L // 2 + 1) / 64
        assert resid < 1e-9, ("B commute", L, resid)
        assert hs2 >= lb
        print(f"  {L:5d} {2*L*L:8d} {resid:20.2e} {hs2:14.4f} {hs2/math.log(L):10.4f} {lb:19.4f}")


if __name__ == "__main__":
    main()
