#!/usr/bin/env python3
"""Search pairs (f, g) in 2V with f g f^-1 = g^2 and g of infinite order.

f ranges over all elements with at most FMAX bricks (sides <= FDEPTH), g over at
most GMAX bricks (sides <= GDEPTH). Uses bs12search.py (unchanged) for the arithmetic.
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

def main():
    fmax, fdepth, gmax, gdepth, shard, nshards = map(int, sys.argv[1:7])
    fs = elements(fmax, fdepth)
    gs = elements(gmax, gdepth)
    tested = found = 0
    for gi, g in enumerate(gs):
        if gi % nshards != shard:
            continue
        g2 = s.compose(g, g)
        # a witness g has infinite order; skip torsion early
        if not s.infinite_order(g, 24):
            continue
        for f in fs:
            tested += 1
            if s.equal(s.compose(s.compose(f, g), s.inverse(f)), g2) and s.infinite_order(g):
                found += 1
                print('WITNESS f=%r g=%r' % (f, g), flush=True)
    print('DONE shard=%d/%d f<=%d(d%d):%d g<=%d(d%d):%d pairs=%d witnesses=%d'
          % (shard, nshards, fmax, fdepth, len(fs), gmax, gdepth, len(gs), tested, found), flush=True)

if __name__ == '__main__':
    main()
