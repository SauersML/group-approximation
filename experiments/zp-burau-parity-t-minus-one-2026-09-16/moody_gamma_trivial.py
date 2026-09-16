#!/usr/bin/env python3
"""Evidence only (not a certificate for any graph node): with Gamma = 1, the
Moody polynomial of the Brunnian braid Phi0 changes, but not at t = -1.

Standard picture: punctures p_1..p_n on a horizontal diameter, base point p_*
at the bottom of the boundary, x_j = straight tail from p_* to p_j plus a
small counterclockwise circle, alpha = [p_1, p_2], beta_*^3 = tail of x_3.
Then c_beta = x_3, the loop class is e_3, and the intersection form I of the
artifact takes the values I(e_1) = eps, I(e_2) = -eps t^{+-1}, I(e_k) = 0 for
k >= 3.  So (1 - t^s) M_{Phi0} = eps (J[3][1] - t^{+-1} J[3][2]) where J is
the matrix of the lifted action, while M_1 = 0.

J is rho_4(w') for w' one of Phi0, rev Phi0, mirror Phi0, rev mirror Phi0,
possibly with t -> 1/t; the fifth strand (f(Phi0) in B_5) only adds a trivial
row and column.  All 16 variants are printed: nonzero over Z[t^{+-1}], zero at
t = -1 (as Corollary A2 of the artifact predicts).
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from burau_minus_one import rho, comm, A, mirror, padd, pmul, peval_m1  # noqa: E402


def psub_inv(p):
    return {-e: c for e, c in p.items()}


def main():
    n = 4
    T2 = [1, 2] * 6
    b = comm(A(1, 4), comm(A(2, 4), A(3, 4)))
    Phi0 = comm(T2, b)
    variants = {
        "w": Phi0,
        "rev": list(reversed(Phi0)),
        "mirror": mirror(Phi0),
        "rev-mirror": list(reversed(mirror(Phi0))),
    }
    ok = True
    for name, w in variants.items():
        R = rho(n, w)
        for inv_t in (False, True):
            c1, c2 = R[2][0], R[2][1]
            if inv_t:
                c1, c2 = psub_inv(c1), psub_inv(c2)
            for s in (1, -1):
                val = padd(c1, pmul({s: 1}, c2), -1)
                nz = bool(val)
                at_m1 = peval_m1(val)
                ok &= nz and at_m1 == 0
                print(name, "t->1/t" if inv_t else "t", "s", s,
                      ": J31 - t^s J32 nonzero:", nz, "; value at t=-1:", at_m1,
                      "; number of terms:", len(val))
    print("ALL VARIANTS NONZERO AND VANISH AT -1:", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
