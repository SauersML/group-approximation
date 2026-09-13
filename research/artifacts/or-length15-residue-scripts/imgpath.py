#!/usr/bin/env python3
"""Recover an explicit Nielsen path from SOURCE to each IMAGE, then re-check it.

Usage: imgpath.py LMAX SOURCE IMAGE [IMAGE ...]

Moves are the elementary Nielsen automorphisms of F(a,t): x -> x y^(+-1) and
x -> y^(+-1) x, for {x,y} = {a,t}. Relators are compared up to cyclic rotation,
inversion and the automorphisms a -> a^-1, t -> t^-1. None of these changes the
group <a,t | w>. This script shares no code with images.py.

For each IMAGE it prints the move sequence found by breadth-first search through
cyclically reduced words of length <= LMAX. It then composes the substitutions
from scratch, applies the composite h to SOURCE, cyclically reduces, and prints
PATH_OK with h(a), h(t) if the result matches IMAGE. Since h is an automorphism,
<a,t | IMAGE> is isomorphic to <a,t | SOURCE>.
"""
import sys
from collections import deque

INV = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def free_reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def cyc(w):
    w = free_reduce(w)
    while len(w) > 1 and w[0] == INV[w[-1]]:
        w = w[1:-1]
    return w


def canon(w):
    cands = []
    for sa in (0, 1):
        for st in (0, 1):
            u = ''.join(INV[x] if (sa and x in 'aA') or (st and x in 'tT') else x for x in w)
            for v in (u, inv(u)):
                cands += [v[i:] + v[:i] for i in range(len(v))]
    return min(cands)


MOVES = [(x, s, side) for x, y in (('a', 't'), ('t', 'a')) for s in (y, INV[y]) for side in 'RL']


def subst(move):
    x, s, side = move
    img = {c: c for c in 'aAtT'}
    img[x] = x + s if side == 'R' else s + x
    img[INV[x]] = inv(img[x])
    return img


def apply(h, w):
    return free_reduce(''.join(h[c] for c in w))


def compose(f, g):
    """Substitution c -> g(f(c)): apply f first, then g."""
    return {c: apply(g, f[c]) for c in 'aAtT'}


def main():
    lmax, src = int(sys.argv[1]), sys.argv[2]
    start = cyc(src)
    parent = {canon(start): None}
    rep = {canon(start): start}
    q = deque([start])
    while q:
        w = q.popleft()
        for m in MOVES:
            u = cyc(apply(subst(m), w))
            if len(u) > lmax:
                continue
            cu = canon(u)
            if cu not in parent:
                parent[cu] = (canon(w), m)
                rep[cu] = u
                q.append(u)
    for target in sys.argv[3:]:
        ct = canon(target)
        if ct not in parent:
            print('NOPATH', src, target)
            continue
        path, cur = [], ct
        while parent[cur] is not None:
            prev, m = parent[cur]
            path.append(m)
            cur = prev
        path.reverse()
        h = {c: c for c in 'aAtT'}
        for m in path:
            h = compose(h, subst(m))
        ok = canon(cyc(apply(h, start))) == ct
        print('PATH' if ok else 'PATH_FAIL', src, target, 'moves=' + ' '.join(''.join(m) for m in path),
              'h(a)=' + h['a'], 'h(t)=' + h['t'], 'PATH_OK' if ok else '')
    print('SENTINEL_DONE')


if __name__ == '__main__':
    main()
