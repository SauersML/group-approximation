#!/usr/bin/env python3
"""j-odometer models: a = (x -> x + 2^j) on Z/2^k, i.e. a is trivial on the top j levels and an odometer on
each of the 2^j subtrees below. Start from ALL tuples (1,b,c,d) in W_j satisfying the relators, lift level by level.
Stored up to conjugation by translations (which commute with a).  usage: bfs2.py J MAXLEVEL [noR]"""
import sys, itertools
import lift as L
from lift import solve, check, order, evalword

def W(j):
    els = [[0]]
    for k in range(j):
        N = 1 << k; new = []
        for p in els:
            for bits in itertools.product((0, 1), repeat=N):
                new.append(L.lift([p], [list(bits)])[0])
        els = new
    return els

def mul(p, q):  # first p then q
    return [q[x] for x in p]

def base(j):
    els = W(j); N = 1 << j; e = list(range(N))
    inv = {tuple(p): L.inv(p) for p in els}
    cube = {tuple(p): mul(mul(p, p), p) for p in els}
    conj = lambda x, y: mul(mul(inv[tuple(y)], x), y)   # x^y
    out = []
    invol = [b for b in els if mul(b, b) == e]
    for b in invol:
        for c in els:
            if conj(c, b) != cube[tuple(c)]: continue
            for d in els:
                if conj(d, c) == cube[tuple(d)]:
                    out.append([e, b, c, d])
    return out

def canon(perms):
    N = len(perms[0]); best = None
    for s in range(N):
        t = tuple(tuple((p[(x - s) % N] + s) % N for x in range(N)) for p in perms[1:])
        if best is None or t < best: best = t
    return best

def lifts(perms, j):
    N = len(perms[0])
    va = [1 if x >= N - (1 << j) else 0 for x in range(N)]
    sol = solve(L.system(perms, free=(1, 2, 3), fixed={0: va}), 3 * N)
    if sol is None: return []
    piv, free = sol; out = []
    for bits in itertools.product((0, 1), repeat=len(free)):
        fv = 0
        for f, bt in zip(free, bits):
            if bt: fv |= 1 << f
        val = fv
        for hb, (m, r) in piv.items():
            if r ^ (bin(m & fv).count("1") & 1): val |= 1 << hb
        vecs = [va] + [[(val >> (g * N + x)) & 1 for x in range(N)] for g in range(3)]
        out.append(L.lift(perms, vecs))
    return out

def main(j, maxlev):
    level = {}
    for t in base(j):
        assert check(t)
        level.setdefault(canon(t), t)
    print("J", j, "base tuples up to translation", len(level), flush=True)
    for k in range(j + 1, maxlev + 1):
        nxt = {}
        for perms in level.values():
            for new in lifts(perms, j):
                assert check(new)
                nxt.setdefault(canon(new), new)
        level = nxt
        prof = {}
        for p in level.values():
            key = tuple(order(q).bit_length() - 1 for q in p)
            prof[key] = prof.get(key, 0) + 1
        print("level", k, "classes", len(level), "max log2 ord(a,b,c,d)",
              tuple(max(x[i] for x in prof) for i in range(4)) if prof else None, flush=True)
        if not level:
            print("NO", j, "-ODOMETER MODEL AT LEVEL", k); break

if __name__ == "__main__":
    if len(sys.argv) > 3 and sys.argv[3] == "noR": L.RELS[:] = L.RELS[:4]
    main(int(sys.argv[1]), int(sys.argv[2]))
