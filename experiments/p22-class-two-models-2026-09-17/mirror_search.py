#!/usr/bin/env python3
"""Split class-two models with the right Levi a copy of the left one.

Take involutions as, at, c of range(m) whose operators Lambda_s, Lambda_t have a
nonzero invariant subspace X with Lambda_t Lambda_s = 1 on X (so the W-level
dynamics A = Lambda_s|X is a genuine invertible map, not the identity), and put
b1 = c, bs = as, bt = at on a second copy of range(m).  The W-level relations
R1-R3 on F_2^m (x) F_2^m are then solved exactly (search.nullspace), and each
solution v is tested at C-level by search.test_u.
"""

import random
import sys

from class2 import Model, rand_involution
from search import build_perms, test_u, papply, nullspace, w_level_system


def d(p, a):
    return a ^ papply(p, a)


def trap_subspace(pa, pb, pc, m):
    """Largest subspace X with Lambda_s X, Lambda_t X in X and
    Lambda_t Lambda_s = 1 on X.  Returns a basis (list of ints)."""
    Ls = lambda x: d(pa, d(pc, x))
    Lt = lambda x: d(pb, d(pc, x))
    basis = nullspace(lambda x: Lt(Ls(x)) ^ x, m)
    while True:
        # X' = {x in span(basis) : Ls x, Lt x in span(basis)}
        k = len(basis)
        if k == 0:
            return []
        # membership test via elimination: project onto complement
        piv = {}
        for b in basis:
            r = b
            while r:
                p = r.bit_length() - 1
                if p in piv:
                    r ^= piv[p]
                else:
                    piv[p] = r
                    break

        def resid(y):
            while y:
                p = y.bit_length() - 1
                if p in piv:
                    y ^= piv[p]
                else:
                    return y
            return 0

        # linear map on coefficient vectors
        def fn(coef):
            x = 0
            for i in range(k):
                if coef >> i & 1:
                    x ^= basis[i]
            return resid(Ls(x)) | (resid(Lt(x)) << m)

        ker = nullspace(fn, k)
        new = []
        for coef in ker:
            x = 0
            for i in range(k):
                if coef >> i & 1:
                    x ^= basis[i]
            new.append(x)
        if len(new) == k:
            return basis
        basis = new


def run(m, configs, rng, n_v=3):
    M = Model(m * m)
    stats = {"left_ok": 0, "wker": 0, "tried": 0, "nontriv_A": 0}
    hits = []
    for _ in range(configs):
        pa, pb, pc = (tuple(rand_involution(m, rng)) for _ in range(3))
        if pa == pb:
            continue
        X = trap_subspace(pa, pb, pc, m)
        if not X:
            continue
        stats["left_ok"] += 1
        if any(d(pa, d(pc, x)) != x for x in X):
            stats["nontriv_A"] += 1
        pl = {"as": pa, "at": pb, "c": pc}
        pr = {"b1": pc, "bs": pa, "bt": pb}
        perms = build_perms(pl, pr, m, m)
        fn, Ls, Lt = w_level_system(perms, m * m)
        ker = nullspace(fn, m * m)
        if not ker:
            continue
        stats["wker"] += 1
        for _ in range(n_v):
            v = 0
            while not v:
                for kv in ker:
                    if rng.random() < 0.5:
                        v ^= kv
            for cu in [0, rng.getrandbits(M.npairs)]:
                stats["tried"] += 1
                ok, E, vals = test_u(M, perms, v, cu)
                if ok:
                    hits.append((pl, v, cu, len(E.rows), M.npairs))
    return hits, stats


MODPOLY = {4: 0b111, 8: 0b1011, 16: 0b10011}


def gf_mul(a, b, q):
    k = q.bit_length() - 1
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> k & 1:
            a ^= MODPOLY[q]
    return r


def gf_inv(a, q):
    for b in range(1, q):
        if gf_mul(a, b, q) == 1:
            return b
    raise ValueError


def field_perms(q, xs, space):
    """as = x_12(xs), at = x_12(xs^{-1}), c = x_21(1) acting on
    space = 'P1' (projective line) or 'V' (nonzero vectors of F_q^2)."""
    if space == "V":
        pts = [(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)]

        def norm(p):
            return p
    else:
        pts = [(a, 1) for a in range(q)] + [(1, 0)]

        def norm(p):
            a, b = p
            if b:
                ib = gf_inv(b, q)
                return (gf_mul(a, ib, q), 1)
            return (1, 0)
    index = {p: i for i, p in enumerate(pts)}

    def perm_of(mat):
        (m11, m12), (m21, m22) = mat
        out = []
        for (a, b) in pts:
            img = (gf_mul(m11, a, q) ^ gf_mul(m12, b, q),
                   gf_mul(m21, a, q) ^ gf_mul(m22, b, q))
            out.append(index[norm(img)])
        return tuple(out)

    xt = gf_inv(xs, q)
    return (perm_of(((1, xs), (0, 1))), perm_of(((1, xt), (0, 1))),
            perm_of(((1, 0), (1, 1)))), len(pts)


def run_field(q, space, rng, n_v=6):
    stats = {"wkerdim": 0, "tried": 0, "nontriv_A": False}
    hits = []
    for xs in range(2, q):
        (pa, pb, pc), m = field_perms(q, xs, space)
        X = trap_subspace(pa, pb, pc, m)
        stats["nontriv_A"] |= any(d(pa, d(pc, x)) != x for x in X)
        pl = {"as": pa, "at": pb, "c": pc}
        pr = {"b1": pc, "bs": pa, "bt": pb}
        perms = build_perms(pl, pr, m, m)
        fn, Ls, Lt = w_level_system(perms, m * m)
        ker = nullspace(fn, m * m)
        stats["wkerdim"] = max(stats["wkerdim"], len(ker))
        if not ker:
            continue
        M = Model(m * m)
        for _ in range(n_v):
            v = 0
            while not v:
                for kv in ker:
                    if rng.random() < 0.5:
                        v ^= kv
            for cu in [0, rng.getrandbits(M.npairs)]:
                stats["tried"] += 1
                ok, E, vals = test_u(M, perms, v, cu)
                if ok:
                    hits.append((q, space, xs, v, cu, len(E.rows), M.npairs))
    return hits, stats


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    configs = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(seed)
    for q, space in [(4, "P1"), (8, "P1"), (4, "V")]:
        hits, st = run_field(q, space, rng)
        print("field q=%d %s: %s, %d hits" % (q, space, st, len(hits)))
        for h in hits[:3]:
            print("  HIT", h)
        if hits:
            return hits
    for m in [4, 5, 6, 7]:
        hits, st = run(m, configs, rng)
        print("mirror m=%d: %s, %d hits" % (m, st, len(hits)))
        for h in hits[:3]:
            print("  HIT", h)
        if hits:
            return hits
    return []


if __name__ == "__main__":
    main()
