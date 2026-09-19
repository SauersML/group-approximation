#!/usr/bin/env python3
"""The exact optimum of the cogrowth-moment route for Thompson's group F, term by term.

Let c_0..c_N be the number of words of length 2n in {x0^{+-1}, x1^{+-1}} that are
trivial in F, and M_n = c_n/16^n the moments of mu_2, the spectral measure of P^2 at
delta_e, where P = (x0 + x0^-1 + x1 + x1^-1)/4.  Then ||P||^2 = sup supp mu_2.

Any lower bound on ||P||^2 that uses only c_0..c_N is bounded by

    theta*(N) := min { sup supp nu : nu a positive measure with moments M_0..M_N },

because such a nu is indistinguishable from mu_2 by the data.  By the truncated
Hausdorff moment theorem (see the proof node) theta*(N) is the smallest theta for
which the localizing Hankel matrices are positive semidefinite:

    N = 2d+1 odd :  L_d(theta) = (theta M_{i+j} - M_{i+j+1})_{i,j<=d}  psd
    N = 2d even  :  H_{d-1}(theta) = (theta M_{i+j+1} - M_{i+j+2})_{i,j<=d-1} psd
                    together with (M_{i+j})_{i,j<=d} psd, which holds for all theta

so theta*(N) is computed here by exact rational bisection with an exact LDL^T test,
and for each N the script emits
  * a rational theta_lo < theta*(N) with an explicit integer witness vector v making
    the localizing form negative (this is a *proof* that ||P||^2 > theta_lo), and
  * a rational theta_hi > theta*(N) at which the localizing matrix is positive
    definite, hence a representing measure supported in [0, theta_hi] exists (this is
    a *proof* that no argument from c_0..c_N gives more than theta_hi).

The gap theta_hi - theta_lo is driven below 1e-12, so the two together pin the
optimal value of the whole moment route at each N.

Usage:  python3 moment_ceiling.py [--nmax 31] [--out out.json]
"""
import argparse
import json
import math
import os
import sys
from fractions import Fraction

# Elvey Price--Guttmann, arXiv:1706.07571, table "Terms in the cogrowth sequence of
# Thompson's group F" (arXiv source Group-growth23-6.tex, l.296-333).  Identical to
# the list embedded in experiments/thompson-f-cogrowth-2026-09-17/epg_certify.py,
# and re-read from that file below as a transcription check.
EPG = [
    1, 4, 28, 232, 2092, 19884, 196096, 1988452, 20612364, 217561120, 2331456068,
    25311956784, 277937245744, 3082543843552, 34493827011868, 389093033592912,
    4420986174041164, 50566377945667804, 581894842848487960, 6733830314028209908,
    78331435477025276852, 915607264080561034564, 10750847942401254987096,
    126768974481834814357308, 1500753741925909645997904, 17833339046478612301547884,
    212663448005862463186139032, 2544535423071442709522261116,
    30542557512715560857221200908, 367718694478039302564802454628,
    4439941127401928226610731571976, 53756708216952135677787623701460,
]

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def prior_table():
    """Re-read the same 32 terms from last wave's script, as a transcription check."""
    path = os.path.join(REPO, "experiments/thompson-f-cogrowth-2026-09-17/epg_certify.py")
    src = open(path).read()
    blk = src.split("EPG = [")[1].split("]")[0]
    return [int(t) for t in blk.replace("\n", " ").split(",") if t.strip()]


def ldl(A):
    """Exact LDL^T. Returns None if positive definite, else (k, d_k, v) with
    v supported on 0..k and v^T A v = d_k <= 0.  A zero pivot stops the
    factorization, and is reported with d_k = 0 (no strict witness)."""
    n = len(A)
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    for i in range(n):
        for j in range(i + 1):
            s = A[i][j] - sum(L[i][t] * L[j][t] * D[t] for t in range(j))
            if i == j:
                D[i] = s
                L[i][i] = Fraction(1)
            else:
                L[i][j] = s / D[j]
        if D[i] <= 0:
            v = [Fraction(0)] * n
            v[i] = Fraction(1)
            for r in range(i - 1, -1, -1):
                v[r] = -sum(L[t][r] * v[t] for t in range(r + 1, i + 1))
            return i, D[i], v
    return None


def localizing(M, N, theta):
    """The matrix whose psd-ness is equivalent to a representing measure on [0,theta]
    existing for the moments M_0..M_N (with (M_{i+j}) psd, which the data satisfy)."""
    if N % 2 == 1:
        d = (N - 1) // 2
        return [[theta * M[i + j] - M[i + j + 1] for j in range(d + 1)] for i in range(d + 1)]
    d = N // 2
    return [[theta * M[i + j + 1] - M[i + j + 2] for j in range(d)] for i in range(d)]


def hankel(M, N):
    d = N // 2
    return [[M[i + j] for j in range(d + 1)] for i in range(d + 1)]


def optimum(M, N, bits=44):
    """(lo, hi): lo has a strictly negative direction (so ||P||^2 > lo is proved),
    hi makes the localizing matrix positive definite (so nothing above hi follows
    from these moments)."""
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if ldl(localizing(M, N, mid)) is not None:
            lo = mid
        else:
            hi = mid
    step = hi - lo
    while True:
        res = ldl(localizing(M, N, lo))
        if res is not None and res[1] < 0:
            return lo, hi
        lo -= step


def integer_witness(A):
    res = ldl(A)
    assert res is not None
    k, dk, v = res
    den = 1
    for x in v:
        den = den * x.denominator // math.gcd(den, x.denominator)
    vi = [int(x * den) for x in v[: k + 1]]
    val = sum(Fraction(vi[i]) * vi[j] * A[i][j] for i in range(len(vi)) for j in range(len(vi)))
    assert val < 0
    return vi, val


def rational_sqrt_floor(theta, digits=10 ** 12):
    r = Fraction(math.isqrt(int(theta * digits * digits)), digits)
    assert r * r <= theta
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=31)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()

    check = prior_table()
    M = [Fraction(x, 16 ** j) for j, x in enumerate(EPG)]
    rows = []
    for N in range(1, a.nmax + 1):
        lo, hi = optimum(M, N)
        A = localizing(M, N, lo)
        vi, val = integer_witness(A)
        assert ldl(localizing(M, N, hi)) is None, N      # psd at hi: the ceiling
        assert ldl(hankel(M, N)) is None, N              # Hankel pd: data are moments
        r = rational_sqrt_floor(lo)
        rows.append({
            "N": N, "word_length": 2 * N,
            "matrix_size": len(A),
            "theta_lower_rational": f"{lo.numerator}/{lo.denominator}",
            "theta_lower": float(lo), "theta_upper": float(hi),
            "rho_certified": float(r),
            "rho_certified_rational": f"{r.numerator}/{r.denominator}",
            "mu_certified": float(16 * lo),
            "witness_len": len(vi),
            "witness_form_value_negative": val < 0,
        })
        print(f"N={N:2d} len={2*N:3d} theta in [{float(lo):.12f}, {float(hi):.12f}] "
              f"rho >= {float(r):.6f}  mu >= {float(16*lo):.6f}", file=sys.stderr, flush=True)

    out = {
        "source": "Elvey Price-Guttmann arXiv:1706.07571, 32 terms",
        "transcription_matches_2026_09_17_script": check == EPG,
        "note": ("theta_lower is certified by an explicit integer vector making the "
                 "localizing form negative; theta_upper is certified by positive "
                 "definiteness of the same matrix, which by the truncated Hausdorff "
                 "moment theorem produces a measure on [0, theta_upper] with exactly "
                 "these moments.  No bound above theta_upper follows from c_0..c_N."),
        "rows": rows,
        "best": rows[-1],
        "increments_of_rho": [round(rows[i]["rho_certified"] - rows[i - 1]["rho_certified"], 8)
                              for i in range(1, len(rows))],
    }
    text = json.dumps(out, indent=1)
    if a.out:
        open(a.out, "w").write(text + "\n")
    else:
        print(text)


if __name__ == "__main__":
    main()
