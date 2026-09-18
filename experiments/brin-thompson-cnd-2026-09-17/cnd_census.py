"""Census: which natural size functions psi on 2V are conditionally negative definite (cnd)?

For a finite set S = {g_1..g_n} we form K_ij = psi(g_i^{-1} g_j) and compute the largest
eigenvalue of P K P (P = projection onto zero-sum vectors). psi cnd  =>  lambda_max <= 0.

Candidates (L = exact minimal brick count, lambda = Lebesgue measure on C^2):
  lin    L - 1                      (on V x 1 this is Farley's caret count: cnd)
  log    log L                      (Bernstein transform of lin: cnd on V x 1)
  sqrt   sqrt(L) - 1
  aniso  int |a_x - a_y| d lambda + same for g^{-1}   (exponent-cocycle anisotropy)
  expo   int (|a_x| + |a_y|) d lambda + same for g^{-1}

Usage: python3 cnd_census.py [--seed S] [--n N] [--len L] [--subgroup 2v|vx1]
"""
import argparse
import math
import random
import numpy as np

import lib2v as V

LETTERS_VX1 = ["x0x", "x1x", "c0x", "c1x", "pix"]


def cand_values(g):
    L = V.min_bricks(g)
    gi = V.inverse(g)
    aniso = sum(float(a) * abs(ax - ay) for a, ax, ay in V.exponent_profile(g)) + \
        sum(float(a) * abs(ax - ay) for a, ax, ay in V.exponent_profile(gi))
    expo = sum(float(a) * (abs(ax) + abs(ay)) for a, ax, ay in V.exponent_profile(g)) + \
        sum(float(a) * (abs(ax) + abs(ay)) for a, ax, ay in V.exponent_profile(gi))
    return {"L": L, "lin": L - 1, "log": math.log(L), "sqrt": math.sqrt(L) - 1,
            "aniso": aniso, "expo": expo}


def sample_set(n, maxlen, rng, letters=None):
    S = []
    seen = []
    while len(S) < n:
        w = V.random_word(rng.randint(0, maxlen), rng, letters)
        g = V.word_element(w)
        if any(V.is_identity(V.compose(V.inverse(h), g)) for h in seen):
            continue
        seen.append(g)
        S.append((w, g))
    return S


def kernels(S):
    n = len(S)
    names = ["L", "lin", "log", "sqrt", "aniso", "expo"]
    K = {k: np.zeros((n, n)) for k in names}
    for i in range(n):
        gi_inv = V.inverse(S[i][1])
        for j in range(i, n):
            vals = cand_values(V.reduce_greedy(V.compose(gi_inv, S[j][1])))
            for k in names:
                K[k][i, j] = K[k][j, i] = vals[k]
    return K


def top_zero_sum(Kmat):
    n = Kmat.shape[0]
    P = np.eye(n) - np.ones((n, n)) / n
    w, U = np.linalg.eigh(P @ Kmat @ P)
    return w[-1], U[:, -1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=40)
    ap.add_argument("--len", type=int, default=4)
    ap.add_argument("--subgroup", default="2v")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    letters = LETTERS_VX1 if args.subgroup == "vx1" else None
    S = sample_set(args.n, args.len, rng, letters)
    K = kernels(S)
    print(f"subgroup={args.subgroup} n={args.n} len<={args.len} seed={args.seed} "
          f"max L={int(K['L'].max())}")
    for k in ["lin", "log", "sqrt", "aniso", "expo"]:
        lam, _ = top_zero_sum(K[k])
        print(f"  {k:6s} lambda_max on zero-sum = {lam:+.6f}  scale={np.abs(K[k]).max():.3f}")


if __name__ == "__main__":
    main()
