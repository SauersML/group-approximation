#!/usr/bin/env python3
"""Check part (2) of z8-rips-scale-10-reduces-to-top-shell-link-collapses.

usage: topshell.py O.txt[.gz] [T.txt[.gz]]

Enumerates T = { x in Lmax_8 at r = 10 : |x|_1 = 10, x_8 = 0, and the nonzero |x_i| form a
7-part partition of 10 or the partition (3,2,2,1,1,1) } directly from its definition. Checks that
T is a subset of O, and that T equals { x in O : |x|_1 = 10, x_8 = 0 }. If a second file is given,
it also checks that the file lists exactly T.  Prints a profile table.
"""
import gzip, sys
from collections import Counter

N, R = 8, 10
PROFILES = {(4, 1, 1, 1, 1, 1, 1), (3, 2, 1, 1, 1, 1, 1), (2, 2, 2, 1, 1, 1, 1), (3, 2, 2, 1, 1, 1)}


def load(fn):
    op = gzip.open if fn.endswith('.gz') else open
    with op(fn, 'rt') as f:
        pts = [tuple(map(int, l.split())) for l in f if l.strip()]
    for p in pts:
        assert len(p) == N, p
    s = set(pts)
    assert len(s) == len(pts), 'duplicate points in ' + fn
    return s


def positive(p):
    for v in reversed(p):
        if v:
            return v > 0
    return False


def profile(p):
    return tuple(sorted((abs(v) for v in p if v), reverse=True))


def enum_T():
    out = []
    def rec(cur, rem):
        if len(cur) == N - 1:
            if rem == 0:
                p = tuple(cur) + (0,)
                if positive(p) and profile(p) in PROFILES:
                    out.append(p)
            return
        for v in range(-rem, rem + 1):
            cur.append(v); rec(cur, rem - abs(v)); cur.pop()
    rec([], R)
    return set(out)


def main():
    O = load(sys.argv[1])
    for p in O:
        assert sum(map(abs, p)) <= R and positive(p), ('not in Lmax_8', p)
    T = enum_T()
    top0 = {p for p in O if sum(map(abs, p)) == R and p[N - 1] == 0}
    print('|O| =', len(O), ' |T| (from definition) =', len(T), ' |{x in O: |x|=10, x_8=0}| =', len(top0))
    assert T <= O, 'T is not contained in O'
    assert top0 == T, 'the norm-10, x_8 = 0 part of O is not T'
    if len(sys.argv) > 2:
        assert load(sys.argv[2]) == T, 'second file is not T'
        print('second file lists exactly T')
    def last(p):
        return max(i for i in range(N) if p[i]) + 1
    c = Counter((last(p), profile(p), sum(1 for v in p if v)) for p in T)
    for k in sorted(c):
        print('  last nonzero index %d, profile %s, support %d: %d' % (k[0], k[1], k[2], c[k]))
    print('TOPSHELL VERIFIED')


if __name__ == '__main__':
    main()
