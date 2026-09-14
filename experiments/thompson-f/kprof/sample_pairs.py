#!/usr/bin/env python3
"""Deterministic pair samples for kernel-dimension profiles of Guba's P_(2,2) over F_2.

Reads s35_unsolved_after_k7.json.gz (the 94329 pairs with no common right multiple of degree <= 7,
landed with eada0577f).  Writes samples.json with:
  stubborn: pairs from the unsolved list, stratified by the x_0-sieve category of 199bac76a
            (both component pairs equal / top equal / bottom equal / both settled);
  solved:   pairs of distinct nonzero elements NOT in the unsolved list (so delta <= 7);
  free_control: pairs for the free-monoid control;
  s24: S_(2,4) calibration pairs.
Seed 20260914.
"""
import gzip, json, random

SEED = 20260914
S = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3)]
nu0 = [sum(1 for x in w if x == 0) for w in S]
lev = {e: sum(1 << i for i in range(9) if nu0[i] == e) for e in (0, 1, 2)}

uns = [tuple(p) for p in json.load(gzip.open("s35_unsolved_after_k7.json.gz"))["unsolved"]]
assert len(uns) == 94329, len(uns)
unsset = set(uns)


def comp(m, e):
    return m & lev[e]


def top(m):
    for e in (2, 1, 0):
        if comp(m, e):
            return comp(m, e)


def bot(m):
    for e in (0, 1, 2):
        if comp(m, e):
            return comp(m, e)


def status(a, b):
    if a == b:
        return "equal"
    p = (min(a, b), max(a, b))
    return "unsolved" if p in unsset else "settled"


cats = {}
for a, b in uns:
    key = status(top(a), top(b)) + "|" + status(bot(a), bot(b))
    cats.setdefault(key, []).append((a, b))

rng = random.Random(SEED)
stubborn = []
for key in sorted(cats):
    pool = cats[key]
    take = min(len(pool), 6)
    for p in rng.sample(pool, take):
        stubborn.append({"a": p[0], "b": p[1], "category": key})

allpairs = [(a, b) for a in range(1, 512) for b in range(a + 1, 512)]
solved_pool = [p for p in allpairs if p not in unsset]
assert len(solved_pool) == 130305 - 94329, len(solved_pool)
solved = [{"a": a, "b": b} for a, b in rng.sample(solved_pool, 24)]

free_control = [{"a": 1, "b": 16}, {"a": 3, "b": 16}, {"a": 7, "b": 56}, {"a": 1, "b": 2}]
s24 = [{"a": 1, "b": 2}, {"a": 1, "b": 4}, {"a": 3, "b": 12}, {"a": 5, "b": 26}, {"a": 7, "b": 25}]

json.dump({"seed": SEED, "category_sizes": {k: len(v) for k, v in sorted(cats.items())},
           "stubborn": stubborn, "solved": solved, "free_control": free_control, "s24": s24},
          open("samples.json", "w"), indent=1)
print({k: len(v) for k, v in sorted(cats.items())}, "stubborn", len(stubborn), "solved", len(solved))
