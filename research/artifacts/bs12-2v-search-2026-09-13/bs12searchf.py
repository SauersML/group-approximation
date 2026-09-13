#!/usr/bin/env python3
"""Search pairs (f, g) in 2V with f g f^-1 = g^2 and g of infinite order.

f ranges over all non-identity elements with at most FMAX bricks (sides <= FDEPTH),
g over at most GMAX bricks (sides <= GDEPTH). Uses bs12search.py (unchanged) for the
arithmetic. The conjugation test runs first; order is examined only for solutions,
with a table-size guard, because powers of baker-like elements have tables that
double in size (job 705555 was OOM-killed by an early order filter).
Usage: bs12searchf.py FMAX FDEPTH GMAX GDEPTH SHARD NSHARDS
"""
import sys, itertools
import bs12search as s

def elements(nmax, depth):
    out = []
    for n in range(1, nmax + 1):
        for D in s.decompositions(n, depth):
            for R in s.decompositions(n, depth):
                for perm in itertools.permutations(range(n)):
                    g = tuple((D[i], R[perm[i]]) for i in range(n))
                    if not s.is_identity(g):
                        out.append(g)
    return out

def order_status(g, cap=48, maxbricks=20000):
    p = g
    for _ in range(cap):
        if s.is_identity(p):
            return 'finite'
        if len(p) > maxbricks:
            return 'unknown'
        p = s.compose(g, p)
    return 'infinite?'

def main():
    fmax, fdepth, gmax, gdepth, shard, nshards = map(int, sys.argv[1:7])
    fs = elements(fmax, fdepth)
    gs = elements(gmax, gdepth)
    tested = torsion = found = unknown = 0
    for gi, g in enumerate(gs):
        if gi % nshards != shard:
            continue
        g2 = s.compose(g, g)
        for f in fs:
            tested += 1
            if not s.equal(s.compose(s.compose(f, g), s.inverse(f)), g2):
                continue
            st = order_status(g)
            if st == 'finite':
                torsion += 1
            elif st == 'unknown':
                unknown += 1
                print('CANDIDATE f=%r g=%r' % (f, g), flush=True)
            else:
                found += 1
                print('WITNESS f=%r g=%r' % (f, g), flush=True)
    print('DONE shard=%d/%d f<=%d(d%d):%d g<=%d(d%d):%d pairs=%d torsion_solutions=%d candidates=%d witnesses=%d'
          % (shard, nshards, fmax, fdepth, len(fs), gmax, gdepth, len(gs), tested, torsion, unknown, found), flush=True)

if __name__ == '__main__':
    main()
