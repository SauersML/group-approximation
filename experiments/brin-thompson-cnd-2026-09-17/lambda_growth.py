"""Does the failure of cnd for log L on 2V grow with the test set?

lambda(S) = top eigenvalue of P K P, K_ij = F(L(g_i^{-1} g_j)).  F(L) + M(1 - delta_e) is cnd
for some constant M iff sup_S lambda(S) <= M, so unbounded lambda(S) kills the candidate even
up to adding a multiple of the (cnd) kernel 1 - delta_e.

Two experiments:
  random : lambda for random sets of growing size n
  greedy : from a pool of random elements, add greedily the element maximising lambda

Candidates F: log L, (log L)^2, (log L)^b for b = 0.5, 0.6, 0.75, 0.9, log(1 + log L).
Usage: python3 lambda_growth.py --mode random|greedy [--target log] [--pool 400] [--len 6] [--seed 11]
"""
import argparse
import math
import random
from multiprocessing import Pool

import numpy as np

import lib2v as V
import cnd_census as C

FS = {
    "log": lambda L: math.log(L),
    "log^2": lambda L: math.log(L) ** 2,
    "sqrt(log)": lambda L: math.sqrt(math.log(L)),
    "loglog": lambda L: math.log(1 + math.log(L)),
    "log^0.9": lambda L: math.log(L) ** 0.9,
    "log^0.75": lambda L: math.log(L) ** 0.75,
    "log^0.6": lambda L: math.log(L) ** 0.6,
}

_ELTS = None


def _init(elts):
    global _ELTS
    _ELTS = elts


def _row(i):
    gi = V.inverse(_ELTS[i])
    return [V.min_bricks(V.reduce_greedy(V.compose(gi, _ELTS[j]))) for j in range(len(_ELTS))]


def L_matrix(elts, procs=4):
    with Pool(procs, initializer=_init, initargs=(elts,)) as p:
        rows = p.map(_row, range(len(elts)))
    return np.array(rows, dtype=float)


def lam(M, idx=None):
    if idx is not None:
        M = M[np.ix_(idx, idx)]
    return C.top_zero_sum(M)[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="random")
    ap.add_argument("--pool", type=int, default=320)
    ap.add_argument("--len", type=int, default=6)
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--steps", type=int, default=60)
    ap.add_argument("--target", default="log")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    S = C.sample_set(args.pool, args.len, rng)
    Lm = L_matrix([g for _, g in S])
    Ks = {k: np.vectorize(f)(Lm) for k, f in FS.items()}
    print(f"pool={args.pool} len<={args.len} seed={args.seed} maxL={int(Lm.max())}")
    if args.mode == "random":
        n = 20
        while n <= args.pool:
            idx = list(range(n))
            print(f"  n={n:4d} " + "  ".join(f"{k}={lam(K, idx):+.2e}" for k, K in Ks.items()))
            n *= 2
        return
    K = Ks[args.target]
    idx = []
    rest = list(range(len(S)))
    for step in range(args.steps):
        best = None
        for r in rest:
            l2 = lam(K, idx + [r]) if len(idx) >= 1 else 0.0
            if best is None or l2 > best[0]:
                best = (l2, r)
        idx.append(best[1])
        rest.remove(best[1])
        if len(idx) % 5 == 0:
            print(f"  greedy size={len(idx):3d} lambda_{args.target}={best[0]:+.3e}", flush=True)


if __name__ == "__main__":
    main()
