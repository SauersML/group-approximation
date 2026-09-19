#!/usr/bin/env python3
"""Enumerate homomorphisms A_K -> S_n (u1 up to conjugacy) and test the
twisted Alexander rank of the permutation representation (and of the
permutation representation tensored with a sign-type abelian twist).

usage: perm_search.py n [maxreport] [p k]   (p k: work over GF(p^k), else mod 1000003)
"""
import sys, itertools, json
import numpy as np
from twisted_alexander import twisted_defect, U1, U2, V1, V2

n = int(sys.argv[1])
maxreport = int(sys.argv[2]) if len(sys.argv) > 2 else 20
GFMODE = len(sys.argv) > 4
if GFMODE:
    import random
    from gfq import GF
    from perm_fox_gfq import defect_gfq
    FQ = GF(int(sys.argv[3]), int(sys.argv[4]))
    RNG = random.Random(7)

perms = np.array(list(itertools.permutations(range(n))), dtype=np.int16)
N = len(perms)
index = {tuple(p): i for i, p in enumerate(perms)}


def comp(a, b):
    # (a*b)(x) = a(b(x)) ; we use left actions: word x1 x2 acts as x1(x2(.))
    return a[b]


def comp_many(a, B):
    # a fixed, B array of perms: a o B
    return a[B]


def many_comp(A, b):
    return A[:, b]


def power_word_many(a, B, m):
    """for fixed a and array B: prod(a,B;m) and prod(B,a;m)"""
    k = B.shape[0]
    x = np.tile(np.arange(n, dtype=np.int16), (k, 1))
    y = x.copy()
    for s in range(m):
        # append generator on the right: x <- x o g
        if s % 2 == 0:
            x = x[:, a]                       # x o a
            y = np.take_along_axis(y, B, 1)   # y o B
        else:
            x = np.take_along_axis(x, B, 1)
            y = y[:, a]
    return x, y


def rel_ok(a, B, m):
    x, y = power_word_many(a, B, m)
    return np.all(x == y, axis=1)


def cycle_type(p):
    seen = [False] * n
    ct = []
    for i in range(n):
        if not seen[i]:
            c = 0
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
                c += 1
            ct.append(c)
    return tuple(sorted(ct))


reps = {}
for i, p in enumerate(perms):
    ct = cycle_type(p)
    if ct not in reps:
        reps[ct] = i

homs = []
for ct, i1 in reps.items():
    a = perms[i1]
    c2 = rel_ok(a, perms, 2)
    for i2 in np.nonzero(c2)[0]:
        b = perms[i2]
        okv1 = rel_ok(a, perms, 4) & rel_ok(b, perms, 4)
        v2base = rel_ok(b, perms, 4) & rel_ok(a, perms, 6)
        for j1 in np.nonzero(okv1)[0]:
            c = perms[j1]
            okv2 = v2base & rel_ok(c, perms, 2)
            for j2 in np.nonzero(okv2)[0]:
                homs.append((i1, int(i2), int(j1), int(j2)))

print("n", n, "homs (u1 up to conj):", len(homs), flush=True)


def pmat(p):
    M = np.zeros((n, n), dtype=np.int64)
    for x in range(n):
        M[p[x], x] = 1
    return M


def orbits_size(gs):
    # size of image group generated
    seen = {tuple(range(n))}
    frontier = [tuple(range(n))]
    gl = [tuple(g) for g in gs]
    while frontier:
        nf = []
        for h in frontier:
            for g in gl:
                k = tuple(g[h[x]] for x in range(n))
                if k not in seen:
                    seen.add(k)
                    nf.append(k)
        frontier = nf
    return len(seen)


found = []
stats = {}
seen_keys = set()
for h in homs:
    gens = [perms[i] for i in h]
    if GFMODE:
        r, full = defect_gfq(FQ, gens, RNG, trials=2)
        r1 = None
    else:
        mats = [pmat(g) for g in gens]
        r, full, r1 = twisted_defect(mats, trials=2)
    key = (r, full)
    stats[key] = stats.get(key, 0) + 1
    if r < full:
        order = orbits_size(gens)
        rec = {"gens": [list(map(int, g)) for g in gens], "rank": r, "full": full,
               "d1": r1, "image_order": order}
        if len(found) < maxreport:
            print("DEFICIENT", rec, flush=True)
        found.append(rec)

print("stats (rank, 3d): count", {str(k): v for k, v in stats.items()})
print("deficient total", len(found))
tag = f"_p{sys.argv[3]}" if GFMODE else ""
json.dump(found[:200], open(f"perm_search_S{n}{tag}.json", "w"))
