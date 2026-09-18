#!/usr/bin/env python3
"""Scaling run: greedy seeding plus reverse-delete pruning on PSL(2,p).

Usage: prune_scale.py SEED PRIMES TRIALS
Reverse-delete: drop a seed if the remaining seeds still close to all of Q.
The result is an inclusion-minimal seed set (an upper bound for r(Q))."""
import random
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bootstrap_seed import (Bootstrap, psl_mul, psl_random, enumerate_group,
                            subgroup_order, phi, periodic_point)


def greedy_seeds(bs, rng):
    bs.reset()
    seeds = []
    n = bs.n
    order = list(range(n))
    rng.shuffle(order)
    ptr = 0
    while bs.size < n:
        v = None
        while bs.ones:
            k = rng.randrange(len(bs.ones))
            t = bs.ones[k]
            bs.ones[k] = bs.ones[-1]
            bs.ones.pop()
            if bs.cnt[t] == 1:
                free = [w for w in bs.tri[t] if not bs.inS[w]]
                free.sort(key=bs.score, reverse=True)
                v = free[0]
                break
        if v is None:
            while bs.inS[order[ptr]]:
                ptr += 1
            v = order[ptr]
        bs.add(v)
        seeds.append(v)
    return seeds


def closes(bs, seeds):
    bs.reset()
    for v in seeds:
        bs.add(v)
    return bs.size == bs.n


def prune(bs, seeds, rng):
    seeds = list(seeds)
    order = list(range(len(seeds)))
    rng.shuffle(order)
    keep = [True] * len(seeds)
    for i in order:
        keep[i] = False
        if not closes(bs, [s for s, k in zip(seeds, keep) if k]):
            keep[i] = True
    return [s for s, k in zip(seeds, keep) if k]


def main():
    rng = random.Random(int(sys.argv[1]))
    primes = [int(x) for x in sys.argv[2].split(",")]
    trials = int(sys.argv[3])
    for p in primes:
        order = p * (p * p - 1) // 2
        ident = (1, 0, 0, 1)
        mul = (lambda x, y, p=p: psl_mul(x, y, p))
        for mal in (False, True):
            while True:
                al, be = psl_random(p, rng), psl_random(p, rng)
                if mal:
                    be, _ = periodic_point(be, al, mul, ident)
                if subgroup_order(ident, [al, be], mul, order) == order:
                    break
            elts, idx, (ra, rb) = enumerate_group(ident, [al, be], mul)
            bs = Bootstrap(ra, rb)
            best_g, best_p = None, None
            for _ in range(trials):
                s = greedy_seeds(bs, rng)
                best_g = len(s) if best_g is None else min(best_g, len(s))
                if order <= 20000:
                    s2 = prune(bs, s, rng)
                    best_p = len(s2) if best_p is None else min(best_p, len(s2))
            print(dict(group="PSL2(%d)" % p, n=order, mal=mal, greedy=best_g,
                       greedy_ratio=round(best_g / order, 5), pruned=best_p,
                       pruned_ratio=None if best_p is None else round(best_p / order, 5)),
                  flush=True)


if __name__ == "__main__":
    main()
