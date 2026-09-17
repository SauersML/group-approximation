#!/usr/bin/env python3
"""Exact minimum number of doubling breakpoints of order-four permutations of Z/nZ.

S(n) = min { #{x : f(x+1) != 2 f(x)} : f in Sym(Z/nZ), f^4 = id }   (n odd)

By base-two-exponential-permutations-iff-sofic-higman-quotient, Higman's group H4 has a
nontrivial sofic quotient iff S(n) = o(n) along all odd n.

Variant --order K replaces f^4 = id by f^K = id (K in {1,2,3,4}); K=2,3 are calibration cases:
H_2(BS(1,2)) and H_3(BS(1,2)) have trivial image of BS(1,2), so S_2(n), S_3(n) >= kappa*n.
Encoding: one-hot f[x][y]; one-hot g = f^2 via f[x][y] & f[y][z] -> g[x][z];
f^4 = id <=> g involution: g[x][z] -> g[z][x].  Breakpoint literal z_x:
f[x][y] & -z_x -> f[x+1][2y].  Sum z_x <= s via totalizer, s increased until SAT.
Every SAT answer is re-verified in pure Python and printed as a certificate.
"""
import argparse, json, sys, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def breakpoints(f, n, m=2):
    return sum(1 for x in range(n) if f[(x + 1) % n] != (m * f[x]) % n)


def order_ok(f, n, K):
    for x in range(n):
        y = x
        for _ in range(K):
            y = f[y]
        if y != x:
            return False
    return True


def solve(n, K=4, solver='cadical153', smax=None, lb=1, verbose=True, m=2):
    pool = IDPool()
    F = lambda x, y: pool.id(('f', x, y))
    G = lambda x, y: pool.id(('g', x, y))
    Z = lambda x: pool.id(('z', x))
    cl = []

    def exactly_one(lits):
        cl.append(list(lits))
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                cl.append([-lits[i], -lits[j]])

    for x in range(n):
        exactly_one([F(x, y) for y in range(n)])
        exactly_one([F(y, x) for y in range(n)])
    if K == 1:
        for x in range(n):
            cl.append([F(x, x)])
    elif K == 2:
        for x in range(n):
            for y in range(n):
                cl.append([-F(x, y), F(y, x)])
    elif K == 3:
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    cl.append([-F(x, y), -F(y, z), F(z, x)])
    elif K == 4:
        for x in range(n):
            exactly_one([G(x, z) for z in range(n)])
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    cl.append([-F(x, y), -F(y, z), G(x, z)])
                cl.append([-G(x, y), G(y, x)])
    else:
        raise ValueError(K)
    for x in range(n):
        for y in range(n):
            cl.append([-F(x, y), Z(x), F((x + 1) % n, (m * y) % n)])
    zs = [Z(x) for x in range(n)]
    t0 = time.time()
    smax = n if smax is None else smax
    for bound in range(lb, smax + 1):
        enc = CardEnc.atmost(lits=zs, bound=bound, vpool=pool, encoding=EncType.totalizer)
        # fresh solver per bound to keep things simple and sound
        s2 = Solver(name=solver, bootstrap_with=cl + enc.clauses)
        ok = s2.solve()
        if verbose:
            print(f"n={n} m={m} K={K} bound={bound} sat={ok} t={time.time()-t0:.1f}s", flush=True)
        if ok:
            model = set(l for l in s2.get_model() if l > 0)
            f = [next(y for y in range(n) if F(x, y) in model) for x in range(n)]
            assert sorted(f) == list(range(n))
            assert order_ok(f, n, K)
            bp = breakpoints(f, n, m)
            assert bp <= bound
            s2.delete()
            return bp, f
        s2.delete()
    return None, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ns', nargs='+', type=int)
    ap.add_argument('--order', type=int, default=4)
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--lb', type=int, default=1)
    ap.add_argument('--json', default=None)
    ap.add_argument('--base', type=int, default=2, help='multiplier m (calibration: m=3 is known to satisfy the asymptotic statement, KKR GS version)')
    a = ap.parse_args()
    out = []
    for n in a.ns:
        t = time.time()
        bp, f = solve(n, a.order, a.solver, lb=a.lb, m=a.base)
        rec = dict(n=n, base=a.base, order=a.order, S=bp, f=f, seconds=round(time.time() - t, 1))
        print(json.dumps(rec), flush=True)
        out.append(rec)
        if a.json:
            with open(a.json, 'a') as fh:
                fh.write(json.dumps(rec) + '\n')


if __name__ == '__main__':
    main()
