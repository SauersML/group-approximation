#!/usr/bin/env python3
"""Exact minimum of the relaxed defect S'(n) from one-matcher-sequence-gives-sofic-higman-quotient.

S'(n) = min over f in Sym(Z/nZ) of  #{x : f(x+1) != 2 f(x)} + #{x : f^4(2x) != 2 f^4(x)}   (n odd).

--exact-return instead requires f^4(2x) = 2 f^4(x) for all x and counts only breakpoints (S''(n)).
S' <= S'' <= S (S from sat_min_breakpoints.py). Every SAT model is re-verified in pure Python.
"""
import argparse, json, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def defects(f, n):
    bp = sum(1 for x in range(n) if f[(x + 1) % n] != (2 * f[x]) % n)
    h = [f[f[f[f[x]]]] for x in range(n)]
    ret = sum(1 for x in range(n) if h[(2 * x) % n] != (2 * h[x]) % n)
    return bp, ret


def solve(n, exact_return=False, solver='cadical153', verbose=False):
    pool = IDPool()
    F = lambda x, y: pool.id(('f', x, y))
    G = lambda x, y: pool.id(('g', x, y))
    H = lambda x, y: pool.id(('h', x, y))
    Z = lambda x: pool.id(('z', x))
    W = lambda x: pool.id(('w', x))
    cl = []

    def exactly_one(lits):
        cl.append(list(lits))
        cl.extend([-lits[i], -lits[j]] for i in range(len(lits)) for j in range(i + 1, len(lits)))

    for M in (F, G, H):
        for x in range(n):
            exactly_one([M(x, y) for y in range(n)])
            exactly_one([M(y, x) for y in range(n)])
    for x in range(n):
        for y in range(n):
            for z in range(n):
                cl.append([-F(x, y), -F(y, z), G(x, z)])
                cl.append([-G(x, y), -G(y, z), H(x, z)])
    for x in range(n):
        for y in range(n):
            cl.append([-F(x, y), Z(x), F((x + 1) % n, (2 * y) % n)])
            if exact_return:
                cl.append([-H(x, y), H((2 * x) % n, (2 * y) % n)])
            else:
                cl.append([-H(x, y), W(x), H((2 * x) % n, (2 * y) % n)])
    lits = [Z(x) for x in range(n)] + ([] if exact_return else [W(x) for x in range(n)])
    t0 = time.time()
    for bound in range(1, n + 1):
        enc = CardEnc.atmost(lits=lits, bound=bound, vpool=pool, encoding=EncType.totalizer)
        s = Solver(name=solver, bootstrap_with=cl + enc.clauses)
        ok = s.solve()
        if verbose:
            print(f"n={n} exact_return={exact_return} bound={bound} sat={ok} t={time.time()-t0:.1f}s", flush=True)
        if ok:
            model = set(l for l in s.get_model() if l > 0)
            f = [next(y for y in range(n) if F(x, y) in model) for x in range(n)]
            s.delete()
            assert sorted(f) == list(range(n))
            bp, ret = defects(f, n)
            if exact_return:
                assert ret == 0 and bp <= bound
            else:
                assert bp + ret <= bound
            return bp + ret, bp, ret, f
        s.delete()
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ns', nargs='+', type=int)
    ap.add_argument('--exact-return', action='store_true')
    ap.add_argument('--json', default=None)
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    for n in a.ns:
        t = time.time()
        tot, bp, ret, f = solve(n, a.exact_return, verbose=a.v)
        order4 = all(f[f[f[f[x]]]] == x for x in range(n))
        rec = dict(n=n, exact_return=a.exact_return, defect=tot, breakpoints=bp, return_defect=ret,
                   f_order_divides_4=order4, f=f, seconds=round(time.time() - t, 1))
        print(json.dumps({k: v for k, v in rec.items() if k != 'f'}), flush=True)
        if a.json:
            with open(a.json, 'a') as fh:
                fh.write(json.dumps(rec) + '\n')


if __name__ == '__main__':
    main()
