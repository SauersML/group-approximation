#!/usr/bin/env python3
"""Check lelim.c against the Python local elimination and against no
elimination, on 30 random systems over (Z/27)[Z/3]: invariants of the
quotient and the relation lattice of the target vectors must agree.
Usage: gcc -O2 -o $LELIM_BIN lelim.c; LELIM_TMP=<dir> LELIM_BIN=<bin> python3 test_lelim.py
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import local  # noqa: E402
from local import census  # noqa: E402
import equivariant as eq  # noqa: E402

local.MOD = 27


def rnd(ng, k):
    v = {}
    for _ in range(k):
        g = random.randrange(ng)
        v[g] = tuple(random.choice([0, 0, 1, -1, 2, 3, -3]) for _ in range(3))
    return {g: a for g, a in v.items() if any(a)}


def summary(ng, cols, R, V):
    nz = 3 * len(cols)
    Rz = eq.expand([local.shift(r, e) for r in R for e in range(3)], cols)
    Rz += [[local.MOD if i == k else 0 for i in range(nz)] for k in range(nz)]
    Vz = eq.expand(V, cols)
    H = census.hnf_rows(Rz, nz)
    _, inv = census.h1_invariants(H, nz)
    W = census.w_lattice(H, Vz, nz)
    return sorted(inv), census.hnf_rows(W, len(V))


for trial in range(30):
    random.seed(trial)
    ng = random.randrange(5, 30)
    rels = [rnd(ng, random.randrange(1, 5)) for _ in range(random.randrange(3, 40))]
    rels = [r for r in rels if r]
    vs = [rnd(ng, 3) for _ in range(4)]
    vs = [v for v in vs if v] or [{0: (1, 0, 0)}]
    base = summary(ng, list(range(ng)), [local.reduce_vec(r) for r in rels],
                   [local.reduce_vec(v) for v in vs])
    a = summary(ng, *local.eliminate_local(ng, rels, vs))
    b = summary(ng, *local.eliminate_c(ng, rels, vs))
    assert base == a == b, (trial, base, a, b)
print("lelim agrees with python and with no elimination on 30 trials")
