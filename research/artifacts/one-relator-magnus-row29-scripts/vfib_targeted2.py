#!/usr/bin/env python3
"""Metabelian-cover virtual fibring search, version 2 (potential strategy fixed).

Version 1 sampled vertex potentials (pot = 0 plus NSAMP random vectors), which missed the
known index-10 certificate of row 23. This version:
  * enumerates all potentials in {-R..R}^(k-1) when that set has at most POTCAP elements,
    exactly as vfib.py does;
  * otherwise runs NREST restarts of greedy local search from random starts. Each step lowers
    (max cell height span, total span) by changing one coordinate by +-1 inside [-R, R].
    Every visited potential gets the two-sided collapse test.
Any CERT line is re-checked by verify.py, so the heuristic cannot produce a false certificate.

Modes:
  search:   vfib_targeted2.py search WORD PMAX MMAX KMAX LAM R POTCAP NREST
  calcert:  vfib_targeted2.py calcert WORD CERTFILE PMAX MMAX KMAX LAM R POTCAP NREST
            takes the census cover (a, t) from CERTFILE for WORD. It reports whether that cover
            is among the affine candidates, then runs the character loop twice on it: with
            the normal potential rule, and with the heuristic forced (POTCAP = 0).
"""
import sys, itertools, random, re, ast
from math import gcd
from vfib import LET, canon, cover, tree_edges, nullspace, alexander, collapses
from vfib_targeted import is_action, transitive, primes, affine_mod, affine_fp2, product_cyclic

def spans(cells, cp):
    mx, tot = 0, 0
    for cell in cells:
        h, lo, hi = 0, 0, 0
        for e, sg in cell:
            h += sg * cp[e]; lo = min(lo, h); hi = max(hi, h)
        mx = max(mx, hi - lo); tot += hi - lo
    return (mx, tot)

def potentials(k, ends, cells, c, R, POTCAP, NREST, rng):
    if (2 * R + 1) ** (k - 1) <= POTCAP:
        for p in itertools.product(range(-R, R + 1), repeat=k - 1):
            yield (0,) + p
        return
    seen = set()
    def cpof(pot):
        return [c[e] + pot[v] - pot[u] for e, (u, v) in enumerate(ends)]
    for rest in range(NREST):
        pot = [0] + ([0] * (k - 1) if rest == 0 else [rng.randint(-R, R) for _ in range(k - 1)])
        cur = spans(cells, cpof(pot))
        while True:
            t = tuple(pot)
            if t not in seen:
                seen.add(t); yield t
            best, bestpot = cur, None
            for i in range(1, k):
                for d in (-1, 1):
                    if -R <= pot[i] + d <= R:
                        q = pot[:]; q[i] += d
                        sp = spans(cells, cpof(q))
                        if sp < best:
                            best, bestpot = sp, q
            if bestpot is None:
                break
            pot, cur = bestpot, best

def run_cover(s, name, a, t, LAM, R, POTCAP, NREST, rng, emit=True):
    w, k = [LET[ch] for ch in s], len(a)
    ends, cells = cover(w, a, t)
    tree = tree_edges(k, ends)
    non = [e for e in range(2 * k) if e not in tree]
    M = [[sum(sg for (e, sg) in cell if e == f) for f in non] for cell in cells]
    null = nullspace(M, len(non))
    b1, nch, nmon, seen = len(null), 0, 0, set()
    for lam in itertools.product(range(-LAM, LAM + 1), repeat=b1):
        nz = [x for x in lam if x]
        if not nz or nz[0] < 0:
            continue
        cn = [sum(l * v[j] for l, v in zip(lam, null)) for j in range(len(non))]
        g = 0
        for x in cn:
            g = gcd(g, abs(x))
        c = [0] * (2 * k)
        for j, f in enumerate(non):
            c[f] = cn[j] // g
        if tuple(c) in seen:
            continue
        seen.add(tuple(c)); nch += 1
        D = alexander(cells, c, non)
        if not (D is not None and abs(D[0]) == 1 and abs(D[-1]) == 1):
            continue
        nmon += 1
        for pot in potentials(k, ends, cells, c, R, POTCAP, NREST, rng):
            cp = [c[e] + pot[v] - pot[u] for e, (u, v) in enumerate(ends)]
            if collapses(k, ends, cells, cp, rng) and collapses(k, ends, cells, [-x for x in cp], rng):
                if emit:
                    print('CERT %s k=%d a=%s t=%s c=%s pot=%s cp=%s delta=%s' % (s, k, list(a), list(t), c, list(pot), cp, D), flush=True)
                return True, b1, nch, nmon
    return False, b1, nch, nmon

def candidates(s, PMAX, MMAX, KMAX):
    w = [LET[ch] for ch in s]
    base = []
    for p in primes(PMAX):
        for n in (p, p * p, p ** 3):
            if n <= KMAX:
                base.extend(affine_mod(n))
        if p * p <= KMAX:
            base.extend(affine_fp2(p))
    cands, keys = [], set()
    for name, a, t in base:
        for m in range(1, MMAX + 1):
            nm, A, T = (name, a, t) if m == 1 else product_cyclic(name, a, t, m)
            if len(A) > KMAX or not is_action(w, A, T) or not transitive(A, T):
                continue
            key = canon(A, T)
            if key in keys:
                continue
            keys.add(key); cands.append((nm, A, T))
    cands.sort(key=lambda x: len(x[1]))
    return cands, keys

def main():
    mode = sys.argv[1]
    rng = random.Random(29)
    if mode == 'search':
        s, PMAX, MMAX, KMAX, LAM, R, POTCAP, NREST = sys.argv[2], *map(int, sys.argv[3:10])
        cands, _ = candidates(s, PMAX, MMAX, KMAX)
        print('CANDIDATES %s n=%d degrees=%s' % (s, len(cands), sorted({len(x[1]) for x in cands})), flush=True)
        for nm, A, T in cands:
            ok, b1, nch, nmon = run_cover(s, nm, A, T, LAM, R, POTCAP, NREST, rng)
            print('DONE %s | %s k=%d b1=%d chars=%d monic=%d cert=%s' % (s, nm, len(A), b1, nch, nmon, ok), flush=True)
    elif mode == 'calcert':
        s, certfile = sys.argv[2], sys.argv[3]
        PMAX, MMAX, KMAX, LAM, R, POTCAP, NREST = map(int, sys.argv[4:11])
        _, keys = candidates(s, PMAX, MMAX, KMAX)
        for line in open(certfile):
            if not line.startswith('CERT ' + s + ' '):
                continue
            F = {key: ast.literal_eval(val) for key, val in re.findall(r' (\w+)=(\[[^\]]*\])', line)}
            a, t = tuple(F['a']), tuple(F['t'])
            print('CALCOVER %s k=%d in_affine_candidates=%s' % (s, len(a), canon(a, t) in keys), flush=True)
            for label, cap in (('normal', POTCAP), ('heuristic', 0)):
                ok, b1, nch, nmon = run_cover(s, 'census', a, t, LAM, R, cap, NREST, rng, emit=(label == 'normal'))
                print('CALRESULT %s rule=%s k=%d b1=%d chars=%d monic=%d cert=%s' % (s, label, len(a), b1, nch, nmon, ok), flush=True)
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
