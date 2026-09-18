"""Shrink a non-cnd witness for a candidate psi to a small subset by greedy deletion.

Starts from a random set of 2V elements, deletes elements one at a time while the zero-sum
top eigenvalue of K_ij = psi(g_i^{-1} g_j) stays positive, and prints the surviving words.

Usage: python3 shrink_witness.py --cand log --seed 2 --n 80 --len 5
"""
import argparse
import random
import numpy as np

import lib2v as V
import cnd_census as C


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cand", default="log")
    ap.add_argument("--seed", type=int, default=2)
    ap.add_argument("--n", type=int, default=80)
    ap.add_argument("--len", type=int, default=5)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    S = C.sample_set(args.n, args.len, rng)
    K = C.kernels(S)[args.cand]
    idx = list(range(len(S)))
    lam, _ = C.top_zero_sum(K)
    print("start", len(idx), lam)
    improved = True
    while improved:
        improved = False
        best = None
        for r in idx:
            sub = [i for i in idx if i != r]
            l2, _ = C.top_zero_sum(K[np.ix_(sub, sub)])
            if l2 > 1e-9 and (best is None or l2 > best[0]):
                best = (l2, r)
        if best is not None:
            idx.remove(best[1])
            improved = True
    lam, vec = C.top_zero_sum(K[np.ix_(idx, idx)])
    print("final size", len(idx), "lambda", lam)
    for i, c in zip(idx, vec):
        print(f"  c={c:+.4f}  word={' '.join(S[i][0]) or 'e'}  L={V.min_bricks(S[i][1])}")
    print("kernel L values:")
    print(C.kernels([S[i] for i in idx])["L"].astype(int))


if __name__ == "__main__":
    main()
