#!/usr/bin/env python3
"""Split class-two models whose W-level is a tensor of eigenvectors.

W-level solutions of the trap relations are rare for random permutations, so
build them: on the left find permutation involutions as != at, c of range(mL)
and x in F_2^mL with Lambda_s x = Lambda_t x = x; on the right find b1, bs, bt
and y with M_s y = M_t y = y.  Then v = x (x) y solves R1-R3 at W-level, and
also every sum of such tensors does.  The head then lives in the centre C and
search.test_u decides whether it survives the smallest admissible K.
"""

import itertools
import random
import sys

from class2 import Model
from search import build_perms, test_u, papply, nullspace


def involutions(m):
    out = []

    def rec(rest, perm):
        if not rest:
            out.append(tuple(perm))
            return
        i = rest[0]
        rec(rest[1:], perm)
        for j in rest[1:]:
            p = list(perm)
            p[i], p[j] = j, i
            rec([k for k in rest[1:] if k != j], p)

    rec(list(range(m)), list(range(m)))
    return out


def eig_space(p1, p2, pc, m):
    """{x : (1+p1)(1+pc) x = x and (1+p2)(1+pc) x = x}."""
    def d(p, a):
        return a ^ papply(p, a)

    def fn(x):
        return (d(p1, d(pc, x)) ^ x) | ((d(p2, d(pc, x)) ^ x) << m)

    return nullspace(fn, m)


def triples_with_eig(m, limit=None, rng=None):
    invs = [p for p in involutions(m) if p != tuple(range(m))]
    out = []
    for pc in invs:
        for p1 in invs:
            for p2 in invs:
                if p1 == p2:
                    continue
                ker = eig_space(p1, p2, pc, m)
                if ker:
                    out.append((p1, p2, pc, ker))
    if rng is not None and limit is not None and len(out) > limit:
        out = rng.sample(out, limit)
    return out


def tensor(x, y, mL, mR):
    v = 0
    for i in range(mL):
        if x >> i & 1:
            for j in range(mR):
                if y >> j & 1:
                    v |= 1 << (i * mR + j)
    return v


def span_elt(basis, rng):
    v = 0
    while not v:
        for b in basis:
            if rng.random() < 0.5:
                v ^= b
    return v


def run(mL, mR, configs, rng, pool=40):
    L = triples_with_eig(mL, pool, rng)
    R = triples_with_eig(mR, pool, rng)
    M = Model(mL * mR)
    hits, tried = [], 0
    for k in range(configs):
        a1, a2, ac, kx = rng.choice(L)
        b2, b3, b1, ky = rng.choice(R)
        pl = {"as": a1, "at": a2, "c": ac}
        pr = {"b1": b1, "bs": b2, "bt": b3}
        perms = build_perms(pl, pr, mL, mR)
        # v = a random element of X (x) Y (sum of tensors)
        v = 0
        while not v:
            for xb in kx:
                for yb in ky:
                    if rng.random() < 0.5:
                        v ^= tensor(xb, yb, mL, mR)
        for cu in [0, rng.getrandbits(M.npairs)]:
            tried += 1
            ok, E, vals = test_u(M, perms, v, cu)
            if ok:
                hits.append((pl, pr, v, cu, len(E.rows), M.npairs))
    return hits, tried


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    configs = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rng = random.Random(seed)
    for mL, mR in [(5, 5), (6, 5), (6, 6)]:
        hits, tried = run(mL, mR, configs, rng)
        print("eigen %dx%d: %d (v, c_u) tried, %d hits" % (mL, mR, tried, len(hits)))
        for h in hits[:3]:
            print("  HIT", h)
        if hits:
            return hits
    return []


if __name__ == "__main__":
    main()
