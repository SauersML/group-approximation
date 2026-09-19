#!/usr/bin/env python3
"""Exhaustive level-by-level enumeration of odometer models of H4(3)/<<[a,c]^2>> (a = x -> x+1 on Z/2^k).
Every transitive action of a finite 2-group quotient on 2^k points in which a is a 2^k-cycle is W_k-conjugate
to exactly such a tuple (a = odometer). Solutions are stored up to conjugation by <a> (the centralizer of a in W_k).
usage: bfs.py MAXLEVEL [RELSET]   RELSET = full (default) | noR (drop [a,c]^2)"""
import sys, itertools
import lift as L
from lift import system, solve, check, order

def canon(perms):
    N = len(perms[0]); best = None
    for j in range(N):
        t = tuple(tuple((p[(x - j) % N] + j) % N for x in range(N)) for p in perms[1:])
        if best is None or t < best:
            best = t
    return best

def lifts(perms):
    N = len(perms[0])
    va = [0] * N; va[N - 1] = 1
    sol = solve(system(perms, free=(1, 2, 3), fixed={0: va}), 3 * N)
    if sol is None:
        return []
    piv, free = sol
    out = []
    for bits in itertools.product((0, 1), repeat=len(free)):
        fv = 0
        for f, bt in zip(free, bits):
            if bt: fv |= 1 << f
        val = fv
        for hb, (m, r) in piv.items():
            if r ^ (bin(m & fv).count("1") & 1):
                val |= 1 << hb
        vecs = [va] + [[(val >> (g * N + x)) & 1 for x in range(N)] for g in range(3)]
        new = L.lift(perms, vecs)
        out.append(new)
    return out

def main(maxlev):
    level = {canon([[0]] * 4): [[0], [0], [0], [0]]}
    for k in range(1, maxlev + 1):
        nxt = {}; dims = {}
        for perms in level.values():
            ls = lifts(perms)
            dims[len(ls)] = dims.get(len(ls), 0) + 1
            for new in ls:
                assert check(new)
                nxt.setdefault(canon(new), new)
        level = nxt
        prof = {}
        for p in level.values():
            key = tuple(order(q).bit_length() - 1 for q in p)
            prof[key] = prof.get(key, 0) + 1
        print("level", k, "classes", len(level), "lift-count histogram of parents", dims,
              "log2 order profiles", sorted(prof.items()), flush=True)
        if not level:
            print("NO ODOMETER MODEL AT LEVEL", k); break
    return level

if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[2] == "noR":
        L.RELS[:] = L.RELS[:4]
    main(int(sys.argv[1]))
