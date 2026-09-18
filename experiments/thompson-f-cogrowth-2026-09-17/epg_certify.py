#!/usr/bin/env python3
"""Exact certified lower bound on ||P||, P = (x0 + x0^-1 + x1 + x1^-1)/4 on l^2(F),
from the 32 exact cogrowth coefficients printed by Elvey Price and Guttmann.

Data. c[n] = number of words of length 2n in x0^{+-1}, x1^{+-1} trivial in F, n = 0..31.
Source: A. Elvey Price, A. J. Guttmann, "Numerical studies of Thompson's group F and related
groups", Internat. J. Algebra Comput. (2019), arXiv:1706.07571, Table "Terms in the cogrowth
sequence of Thompson's group F" (arXiv source Group-growth23-6.tex, l.296-333).
If a path to that .tex file is given as argv[1], the table is re-parsed from it and compared.

Cross-checks (independent sources):
  n <= 15 : this repository's own computation experiments/thompson-f/out15.json
  n <= 24 : Haagerup-Haagerup-Ramirez-Solano arXiv:1409.1486 Case 2 table, as parsed in
            experiments/thompson-f/hhr_certify.json

Certificate (exact rational arithmetic, no floating point in any asserted step).
  mu_2 = spectral measure of P^2 at delta_e: a probability measure on [0, ||P||^2] with moments
  M_j = c[j]/16^j.  For s in {0,1} and rational theta let
      A_s(theta)_{ij} = theta*M_{i+j+s} - M_{i+j+s+1},   0 <= i,j < d_s,
  so that for q(x) = sum_i v_i x^i,  v^T A_s(theta) v = int x^s q(x)^2 (theta - x) dmu_2(x).
  If mu_2 were supported in [0, theta] the integrand would be >= 0.  Hence an explicit rational
  vector v with v^T A_s(theta) v < 0 proves mu_2((theta, oo)) > 0, so ||P||^2 > theta.
  theta is found by bisection with exact LDL^T; the witness v is then re-verified by direct
  evaluation of the quadratic form.
"""
import json, math, os, re, sys
from fractions import Fraction

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


def parse_tex(path):
    tex = open(path).read()
    blk = tex.split("Coefficients\\\\")[1].split("\\end{tabular}")[0]
    return [int(t) for t in re.findall(r"^\s*(\d+)\\\\", blk, re.M)]


def ldl_first_negative(A):
    """Exact LDL^T. Returns (k, d_k, v) for the first pivot d_k <= 0, with v^T A v = d_k
    (v supported on 0..k), or None if A is positive definite."""
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
            k = i
            # solve L^T v = e_k on indices 0..k
            v = [Fraction(0)] * n
            v[k] = Fraction(1)
            for r in range(k - 1, -1, -1):
                v[r] = -sum(L[t][r] * v[t] for t in range(r + 1, k + 1))
            return k, D[k], v
    return None


def qform(v, A):
    return sum(v[i] * v[j] * A[i][j] for i in range(len(v)) for j in range(len(v)) if v[i] and v[j])


def matrix(M, s, d, theta):
    return [[theta * M[i + j + s] - M[i + j + s + 1] for j in range(d)] for i in range(d)]


def certify(c, s):
    M = [Fraction(x, 16 ** j) for j, x in enumerate(c)]
    N = len(M) - 1              # moments M_0..M_N available
    d = (N - s + 1) // 2        # need index 2(d-1)+s+1 <= N
    lo, hi = Fraction(0), Fraction(1)   # A_s(1) must be PSD-compatible: ||P|| <= 1
    for _ in range(34):
        mid = (lo + hi) / 2
        if ldl_first_negative(matrix(M, s, d, mid)) is not None:
            lo = mid
        else:
            hi = mid
    theta = Fraction(math.floor(lo * 10 ** 9), 10 ** 9)
    A = matrix(M, s, d, theta)
    res = ldl_first_negative(A)
    assert res is not None
    k, dk, v = res
    # scale witness to integers and re-verify directly
    den = 1
    for x in v:
        den = den * x.denominator // math.gcd(den, x.denominator)
    vi = [int(x * den) for x in v]
    val = qform([Fraction(x) for x in vi], A)
    assert val < 0
    r = Fraction(math.isqrt(math.floor(theta * 10 ** 12)), 10 ** 6)
    assert r * r <= theta
    return {
        "s": s, "matrix_size": d, "moments_used": f"M_0..M_{2 * (d - 1) + s + 1}",
        "theta": f"{theta.numerator}/{theta.denominator}",
        "witness_negative_index": k,
        "witness_integer_vector": [str(x) for x in vi[: k + 1]],
        "witness_quadratic_form_negative": val < 0,
        "rho_lower_bound": f"{r.numerator}/{r.denominator}",
        "rho_lower_bound_float": float(r),
        "norm_of_x0+x0inv+x1+x1inv_lower_bound": float(4 * r),
        "cogrowth_rate_mu_lower_bound": float(16 * theta),
    }


def main():
    out = {"n_terms": len(EPG)}
    if len(sys.argv) > 1:
        parsed = parse_tex(sys.argv[1])
        out["tex_parse_matches_embedded"] = parsed == EPG
    try:
        ours = json.load(open(os.path.join(REPO, "experiments/thompson-f/out15.json")))["c2"]
        out["agree_with_repo_out15_n_le_15"] = ours[:16] == EPG[:16]
    except OSError:
        out["agree_with_repo_out15_n_le_15"] = "file missing"
    try:
        hhr = json.load(open(os.path.join(REPO, "experiments/thompson-f/hhr_certify.json")))
        out["agree_with_hhr_n_16_to_24"] = hhr["hhr_c2_16_to_24"] == EPG[16:25]
    except OSError:
        out["agree_with_hhr_n_16_to_24"] = "file missing"
    out["z2_upper_bound_ok"] = all(x <= math.comb(2 * j, j) ** 2 for j, x in enumerate(EPG))
    M = [Fraction(x, 16 ** j) for j, x in enumerate(EPG)]
    out["log_convex"] = all(M[j] ** 2 <= M[j - 1] * M[j + 1] for j in range(1, len(M) - 1))
    out["ratios_c_n_over_c_n_minus_1"] = [round(EPG[j] / EPG[j - 1], 6) for j in range(1, len(EPG))]
    certs = {}
    for label, c in (("N24_hhr_range", EPG[:25]), ("N31_epg_full", EPG)):
        certs[label] = [certify(c, 0), certify(c, 1)]
        print(label, [x["rho_lower_bound"] for x in certs[label]], file=sys.stderr, flush=True)
    out["certificates"] = certs
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
