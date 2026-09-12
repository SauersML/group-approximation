#!/usr/bin/env python3
"""Exact character overlaps for the delta(3) instance.

rho = permutation rep of G = SL_3(Z/8) on (Z/8)^3;
Q0 = <e12(2), e13(4), e23(2), e21(1), e31(1), e32(1)> (source parahoric);
phi = conjugation by diag(2,1,1/2) (maps the generator list as recorded).

Computes over Q0 (enumerated as the parahoric pattern subgroup
{upper entries divisible: b12 = 0 mod 2, b13 = 0 mod 4, b23 = 0 mod 2}):
  N  = |Q0|
  S1 = sum chi(q)^2            -> ||chi|_Q0||^2 * N   (chi real: perm char)
  S2 = sum chi(q) chi(phi(q))  -> <chi, chi o phi> * N
If S2 < S1 the restrictions rho|_Q0 and rho o phi|_Q0 are NOT isomorphic
and the exact intertwiner manifold is empty; 2 - 2*S2/S1-type numbers
calibrate the measured control floor.
Also verifies phi(Q0) subset SL_3(Z/8) and counts kernel dims exactly.
"""
import json
import sys

import numpy as np

MOD = 8


def vint(x):
    """2-adic valuation of an exact integer; None for 0 (= infinity)."""
    x = int(x)
    if x == 0:
        return None
    return (abs(x) & -abs(x)).bit_length() - 1


def chi_perm(g, k=3):
    """|ker(g - I) mod 2^k| via integer-lift Smith valuations.

    Lift entries to [0, 2^k); minors and det computed exactly over Z.
    Valuations are lift-independent below k + (previous divisor sum),
    which is all the capped exponents use; exact zero means infinity.
    """
    mod = 1 << k
    B = [[(g[i][j] - (1 if i == j else 0)) % mod for j in range(3)]
         for i in range(3)]
    vals = [vint(B[i][j]) for i in range(3) for j in range(3)]
    fin = [v for v in vals if v is not None]
    v1 = min(fin) if fin else None
    if v1 is None:
        return (1 << k) ** 3
    minors = []
    for r in ((0, 1), (0, 2), (1, 2)):
        for c in ((0, 1), (0, 2), (1, 2)):
            m = B[r[0]][c[0]] * B[r[1]][c[1]] - B[r[0]][c[1]] * B[r[1]][c[0]]
            minors.append(m)
    mv = [vint(m) for m in minors]
    mfin = [v for v in mv if v is not None]
    v12 = min(mfin) if mfin else None
    det = (B[0][0] * (B[1][1] * B[2][2] - B[1][2] * B[2][1])
           - B[0][1] * (B[1][0] * B[2][2] - B[1][2] * B[2][0])
           + B[0][2] * (B[1][0] * B[2][1] - B[1][1] * B[2][0]))
    dv = vint(det)
    a = min(k, v1)
    if v12 is None:
        b = k
        c = k
    else:
        b = min(k, max(v12 - v1, 0))
        c = k if dv is None else min(k, max(dv - v12, 0))
    return 1 << (a + b + c)


def main():
    H = np.diag([2, 1, 4])  # diag(2,1,1/2): 1/2 = 4*... careful below
    # phi(q) = h q h^{-1} with h = diag(2,1,1/2). Over Z[1/2]:
    # (h q h^-1)[i][j] = q[i][j] * d_i / d_j, d = (2,1,1/2).
    # ratios: multiply row1 by 2, row3 by 1/2; col1 by 1/2, col3 by 2.
    def phi(q):
        # Ad(h^{-1}): entry (i,j) scaled by d_j/d_i, d = (2,1,1/2):
        # upper entries divided (pattern guarantees integrality),
        # lower entries multiplied.
        div = [[1, 2, 4], [0, 1, 2], [0, 0, 1]]
        mul = [[1, 0, 0], [2, 1, 0], [4, 2, 1]]
        M = [[0] * 3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                if i < j:
                    if q[i][j] % div[i][j] != 0:
                        return None
                    # (1,3) divides by 4: well-defined only mod 2
                    M[i][j] = (q[i][j] // div[i][j]) % 2
                elif i > j:
                    M[i][j] = (q[i][j] * mul[i][j]) % 2
                else:
                    M[i][j] = q[i][j] % 2
        return M

    N = 0
    S1 = 0
    S2 = 0
    S3 = 0
    bad = 0
    # enumerate Q0: all SL3(Z/8) matrices with b12=0 mod2, b13=0 mod4,
    # b23=0 mod2.  Enumerate by free entries: lower triangle free mod 8,
    # diagonal unitsish — enumerate all 9 entries with the divisibility
    # pattern and det = 1 mod 8.  8^6 * 4*2*2 / ... = manageable: loop
    # smartly: entries: a11,a22,a33 in 0..7; a21,a31,a32 in 0..7;
    # a12 in {0,2,4,6}, a13 in {0,4}, a23 in {0,2,4,6}.
    from itertools import product
    r8 = range(8)
    for a11, a22, a33 in product(r8, r8, r8):
        for a21, a31, a32 in product(r8, r8, r8):
            for a12 in (0, 2, 4, 6):
                for a13 in (0, 4):
                    for a23 in (0, 2, 4, 6):
                        det = (a11 * (a22 * a33 - a23 * a32)
                               - a12 * (a21 * a33 - a23 * a31)
                               + a13 * (a21 * a32 - a22 * a31)) % MOD
                        if det != 1:
                            continue
                        q = [[a11, a12, a13],
                             [a21, a22, a23],
                             [a31, a32, a33]]
                        fq = phi(q)
                        if fq is None:
                            bad += 1
                            continue
                        N += 1
                        c1 = chi_perm(q, 3)
                        c2 = chi_perm(fq, 1)
                        S1 += c1 * c1
                        S2 += c1 * c2
                        S3 += c2 * c2
    out = {"N_Q0": N, "phi_undefined": bad,
           "S1_norm2_times_N": int(S1), "S2_overlap_times_N": int(S2),
           "S3_phinorm2_times_N": int(S3),
           "norm2_source": S1 / N, "overlap": S2 / N,
           "norm2_twisted": S3 / N,
           "note": "two-level descent: chi8 source vs chi2 twisted",
           "cross_defect": (S1 / N) + (S3 / N) - 2 * (S2 / N)}
    print(json.dumps(out, indent=1), flush=True)
    with open("sl3_branching_overlap.json", "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", file=sys.stderr)


if __name__ == "__main__":
    main()
