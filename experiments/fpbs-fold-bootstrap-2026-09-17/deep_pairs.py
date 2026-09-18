#!/usr/bin/env python3
"""Seed densities for the deep stage pairs H_1 <= H_{m+1} of Gamma_mal.

After the automorphism identifying H_{m+1} with F_2 = <a,b>, the pair is
K_m = <a, phi^m(b)> <= F_2, phi(b) = b a b^-2.  Quotients: Zassenhaus
p-quotients (theta-compatible chain) and random PSL(2,p).
Usage: deep_pairs.py mmax trials
"""
import random
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from general_fold import stallings, phi_word, run_seeding
from pgroup_seed import magnus_quotient
from bootstrap_seed import psl_mul, psl_random, enumerate_group, subgroup_order


def quotients(rng):
    for (p, c) in ((2, 3), (3, 3), (2, 4), (5, 3)):
        ra, rb = magnus_quotient(p, c, 10 ** 6)
        yield "Zass(p=%d,c=%d)" % (p, c), ra, rb
    for p in (13, 19):
        order = p * (p * p - 1) // 2
        ident = (1, 0, 0, 1)
        mul = (lambda x, y, p=p: psl_mul(x, y, p))
        while True:
            al, be = psl_random(p, rng), psl_random(p, rng)
            if subgroup_order(ident, [al, be], mul, order) == order:
                break
        _, _, (ra, rb) = enumerate_group(ident, [al, be], mul)
        yield "PSL2(%d)" % p, ra, rb


def main():
    mmax, trials = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(4242)
    w = [1]
    gens = []
    for m in range(1, mmax + 1):
        w = phi_word(w)
        gens.append((m, list(w)))
    for label, ra, rb in quotients(rng):
        n = len(ra)
        for (m, wm) in gens:
            V, edges = stallings([[0], wm])
            if V * n > 3 * 10 ** 6:
                continue
            res = {}
            for mode in ("random", "lowest"):
                res[mode] = min(run_seeding(V, edges, ra, rb, rng, mode) for _ in range(trials))
            print(dict(Q=label, n=n, m=m, word_len=len(wm), stallings_V=V,
                       random=res["random"], lowest=res["lowest"],
                       best_ratio=round(min(res.values()) / n, 5)), flush=True)


if __name__ == "__main__":
    main()
