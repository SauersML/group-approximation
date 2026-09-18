"""Exact certification of non-cnd witnesses on 2V.

For a candidate psi and a finite set of words g_1..g_n, finds integer coefficients c with
sum c_i = 0 and verifies EXACTLY that  Q = sum_{i,j} c_i c_j psi(g_i^{-1} g_j) > 0.

Exact arithmetic per candidate (L = exact minimal brick count, integer):
  lin    Q = sum c_i c_j (L_ij - 1)                        integer arithmetic
  log    Q > 0  <=>  prod L_ij^{c_i c_j} > 1                big-integer comparison
  sqrt   Q = sum c_i c_j sqrt(L_ij)  (constant killed by zero sum); decimal with 60 digits,
         reported with the rounding bound n^2 * max|c|^2 * 1e-55
  aniso, expo  Fraction arithmetic (areas are dyadic rationals)

Usage:
  python3 certify_witness.py --cand log --seed 2 --n 80 --len 5    (shrink a random set, certify)
  python3 certify_witness.py --cand log --words "x1x;bak' c0y' c1y c0y;x0x c0y;c0y' x1x;x0x"
"""
import argparse
import random
from decimal import Decimal, getcontext
from fractions import Fraction

import numpy as np

import lib2v as V
import cnd_census as C


def exact_values(g):
    L = V.min_bricks(g)
    gi = V.inverse(g)
    prof = V.exponent_profile(g) + V.exponent_profile(gi)
    aniso = sum(a * abs(ax - ay) for a, ax, ay in prof)
    expo = sum(a * (abs(ax) + abs(ay)) for a, ax, ay in prof)
    return {"L": L, "aniso": aniso, "expo": expo}


def exact_kernel(elts):
    n = len(elts)
    K = [[None] * n for _ in range(n)]
    for i in range(n):
        gi = V.inverse(elts[i])
        for j in range(n):
            K[i][j] = exact_values(V.reduce_greedy(V.compose(gi, elts[j])))
    return K


def integer_coeffs(vec, scale):
    c = [int(round(scale * x)) for x in vec]
    s = sum(c)
    k = max(range(len(c)), key=lambda i: abs(c[i]))
    c[k] -= s
    assert sum(c) == 0
    return c


def certify(cand, K, c):
    n = len(c)
    if cand == "lin":
        Q = sum(c[i] * c[j] * (K[i][j]["L"] - 1) for i in range(n) for j in range(n))
        return Q > 0, str(Q)
    if cand == "log":
        num, den = 1, 1
        for i in range(n):
            for j in range(n):
                e = c[i] * c[j]
                if e > 0:
                    num *= K[i][j]["L"] ** e
                elif e < 0:
                    den *= K[i][j]["L"] ** (-e)
        ok = num > den
        ratio = Decimal(num) / Decimal(den)
        return ok, f"prod L^(c_i c_j) = num/den with num>den: {ok}; ratio ~ {ratio:.6e}; " \
                   f"Q = log ratio ~ {float(ratio.ln()):.6e}"
    if cand == "sqrt":
        getcontext().prec = 60
        Q = sum(c[i] * c[j] * Decimal(K[i][j]["L"]).sqrt() for i in range(n) for j in range(n))
        err = Decimal(n * n) * Decimal(max(abs(x) for x in c)) ** 2 * Decimal("1e-55")
        return Q > err, f"Q ~ {Q:.12e} (rounding bound {err:.1e})"
    if cand in ("aniso", "expo"):
        Q = sum(c[i] * c[j] * K[i][j][cand] for i in range(n) for j in range(n))
        return Q > 0, f"Q = {Q} ~ {float(Q):.6e}"
    raise ValueError(cand)


def float_matrix(cand, K):
    import math
    n = len(K)
    M = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            L = K[i][j]["L"]
            M[i, j] = {"lin": L - 1, "log": math.log(L), "sqrt": math.sqrt(L) - 1}.get(cand) \
                if cand in ("lin", "log", "sqrt") else float(K[i][j][cand])
    return M


def shrink(M):
    idx = list(range(M.shape[0]))
    while True:
        best = None
        for r in idx:
            sub = [i for i in idx if i != r]
            l2, _ = C.top_zero_sum(M[np.ix_(sub, sub)])
            if l2 > 1e-9 and (best is None or l2 > best[0]):
                best = (l2, r)
        if best is None:
            return idx
        idx.remove(best[1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cand", default="log")
    ap.add_argument("--seed", type=int, default=2)
    ap.add_argument("--n", type=int, default=80)
    ap.add_argument("--len", type=int, default=5)
    ap.add_argument("--words", default=None)
    ap.add_argument("--scale", type=int, default=1000)
    args = ap.parse_args()
    if args.words:
        words = [w.split() for w in args.words.split(";")]
        elts = [V.word_element(w) for w in words]
    else:
        rng = random.Random(args.seed)
        S = C.sample_set(args.n, args.len, rng)
        M = C.kernels(S)[args.cand]
        idx = shrink(M)
        words = [S[i][0] for i in idx]
        elts = [S[i][1] for i in idx]
    for g in elts:
        V.check(g)
    K = exact_kernel(elts)
    M = float_matrix(args.cand, K)
    lam, vec = C.top_zero_sum(M)
    c = integer_coeffs(vec, args.scale)
    ok, info = certify(args.cand, K, c)
    print(f"candidate={args.cand} size={len(elts)} float lambda_max={lam:+.6e}")
    for w, ci, g in zip(words, c, elts):
        print(f"  c={ci:+d}  word={' '.join(w) or 'e'}  L={V.min_bricks(g)}  bricks={g}")
    print("L matrix:")
    for row in K:
        print("  ", [x["L"] for x in row])
    print("CERTIFIED" if ok else "NOT CERTIFIED", info)


if __name__ == "__main__":
    main()
