#!/usr/bin/env python3
"""Search for locally constant NONABELIAN finite covers separating G0/<<base>> from V.

A depth-k rule assigns sigma_x(p) in Sym(F) to each generator x in {a,b,c} and each binary word
p of length k, giving the skew action (z,i).x = (z.x, i.sigma_x(z[:k])) on C x F (a lift of the
triple to the fibrewise-permutation extension C(C,Sym F) x| V).  The lifted triple satisfies a
relator r iff the ordered product of the voltages around the r-loop is the identity on every
cylinder.  We backtrack over rules satisfying all `base` loops and ask whether some `test`
loop can be nontrivial.  A hit means the test relator is not in the normal closure of `base`
(in the free group on a,b,c), hence not in <<base>>; a miss is inconclusive.

usage: nonabelian_covers.py k F base_csv test_csv [max_solutions]
"""
import itertools
import sys

import prefix_cocycles as pc


def loops(word, k):
    """(cylinder, [(var, sign)]) with var = (letter, prefix) in path order."""
    out = []
    stack = [""]
    need = max(k, pc.NEED)
    while stack:
        p0 = stack.pop()
        s = p0
        seq = []
        ok = True
        for g, e in word:
            if e == 1:
                t = pc.act(s, (g, 1)) if len(s) >= need else None
                if t is None:
                    ok = False
                    break
                seq.append(((g, s[:k]), 1))
                s = t
            else:
                t = pc.act(s, (g, -1))
                if t is None or len(t) < need:
                    ok = False
                    break
                seq.append(((g, t[:k]), -1))
                s = t
        if not ok:
            stack.append(p0 + "0")
            stack.append(p0 + "1")
            continue
        assert s == p0
        out.append((p0, seq))
    return out


def main():
    k = int(sys.argv[1])
    F = int(sys.argv[2])
    base = sys.argv[3].split(",")
    tests = sys.argv[4].split(",")
    max_sol = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 6
    perms = list(itertools.permutations(range(F)))
    pidx = {q: i for i, q in enumerate(perms)}
    ident = pidx[tuple(range(F))]
    n = len(perms)
    # right action: i.(pq) = (i.p).q ; composition table
    mul = [[pidx[tuple(perms[q][perms[p][i]] for i in range(F))] for q in range(n)] for p in range(n)]
    inv = [pidx[tuple(sorted(range(F), key=lambda i: perms[p][i]))] for p in range(n)]
    for p in range(n):
        assert mul[p][inv[p]] == ident

    varlist = [(g, "".join(b)) for g in "abc" for b in itertools.product("01", repeat=k)]
    vid = {v: i for i, v in enumerate(varlist)}
    cons = []
    for name in base:
        for p0, seq in loops(pc.WORDS[name], k):
            cons.append([(vid[v], s) for v, s in seq])
    tcons = []
    for name in tests:
        for p0, seq in loops(pc.WORDS[name], k):
            tcons.append((name, p0, [(vid[v], s) for v, s in seq]))
    nv = len(varlist)
    occ = [[] for _ in range(nv)]
    for ci, c in enumerate(cons):
        for v, _ in c:
            if ci not in occ[v]:
                occ[v].append(ci)
    order = sorted(range(nv), key=lambda v: -len(occ[v]))
    pos = {v: i for i, v in enumerate(order)}
    # each constraint is checked when its last variable (in order) is assigned
    check_at = [[] for _ in range(nv)]
    for ci, c in enumerate(cons):
        last = max(c, key=lambda t: pos[t[0]])[0]
        check_at[last].append(ci)

    val = [None] * nv

    def prod(c):
        x = ident
        for v, s in c:
            x = mul[x][val[v] if s == 1 else inv[val[v]]]
        return x

    stats = {"solutions": 0, "violations": {}}
    found = []

    def rec(i):
        if stats["solutions"] >= max_sol:
            return
        if i == nv:
            stats["solutions"] += 1
            bad = [(nm, p0) for nm, p0, c in tcons if prod(c) != ident]
            for nm, p0 in bad:
                stats["violations"][nm] = stats["violations"].get(nm, 0) + 1
            if bad and len(found) < 3:
                found.append(({varlist[v]: perms[val[v]] for v in range(nv)}, bad[:6]))
            return
        v = order[i]
        for q in range(n):
            val[v] = q
            if all(prod(cons[ci]) == ident for ci in check_at[v]):
                rec(i + 1)
        val[v] = None

    rec(0)
    print({"k": k, "F": F, "base": base, "tests": tests, "vars": nv, "constraints": len(cons), **stats})
    for sol, bad in found:
        print("WITNESS", bad)
        print(sol)


if __name__ == "__main__":
    main()
