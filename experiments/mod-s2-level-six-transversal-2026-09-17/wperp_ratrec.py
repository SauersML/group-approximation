#!/usr/bin/env python3
"""Rational W^perp at level six from the two 31-bit primes (evidence, not proof).

W_p^perp (the row space of Phi_p^T in F_p^900) is intrinsic, so its reduced
row echelon form is too.  The RREF over the two 31-bit primes is combined by
CRT and rational reconstruction.  The result is then checked against the RREF
mod 5, 7, 11 and 13 (all of rank 108).  Output: pickle {"pivots", "rows"} with
Fraction entries.

Usage: python3 wperp_ratrec.py phi.pkl out.pkl
"""
import pickle
import sys
from fractions import Fraction

from flint import nmod_mat


def rref(F, p):
    A = nmod_mat([[F[c][k] % p for c in range(len(F))] for k in range(len(F[0]))], p)
    R, rk = A.rref()
    rows = [[int(R[i, j]) for j in range(R.ncols())] for i in range(rk)]
    piv = [next(j for j in range(len(r)) if r[j]) for r in rows]
    return piv, rows


def ratrec(a, n):
    """a/n -> Fraction with |num|, den <= sqrt(n/2) (Wang), or None."""
    a %= n
    r0, r1, s0, s1 = n, a, 0, 1
    bound = int((n // 2) ** 0.5)
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1)


def main(pkl, out):
    Phi = pickle.load(open(pkl, "rb"))["Phi"]
    p1, p2 = 2147483647, 2147483629
    (pv1, R1), (pv2, R2) = rref(Phi[p1], p1), rref(Phi[p2], p2)
    assert pv1 == pv2, "pivot sets differ"
    n = p1 * p2
    inv = pow(p1, -1, p2)
    rows, fails, maxden, maxnum = [], 0, 1, 0
    for a, b in zip(R1, R2):
        row = []
        for x, y in zip(a, b):
            z = (x + p1 * ((y - x) * inv % p2)) % n
            q = ratrec(z, n)
            if q is None:
                fails += 1
                q = Fraction(0)
            maxden = max(maxden, q.denominator)
            maxnum = max(maxnum, abs(q.numerator))
            row.append(q)
        rows.append(row)
    print("rank", len(rows), "reconstruction failures", fails, "max num", maxnum,
          "max den", maxden, flush=True)
    for p in (5, 7, 11, 13):
        pv, R = rref(Phi[p], p)
        ok = pv == pv1 and all(
            (q.numerator * pow(q.denominator, -1, p) - R[i][j]) % p == 0
            for i, row in enumerate(rows) for j, q in enumerate(row))
        print(f"check mod {p}: pivots equal {pv == pv1}, entries agree {ok}", flush=True)
    pickle.dump({"pivots": pv1, "rows": rows}, open(out, "wb"))


if __name__ == "__main__":
    main(*sys.argv[1:])
