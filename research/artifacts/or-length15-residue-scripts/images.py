#!/usr/bin/env python3
"""Nielsen images of relators, up to a length bound, one per symmetry class.

Usage: images.py LMAX WORD [WORD ...]

Breadth-first search from each WORD under the elementary automorphisms
a -> a t^(+-1), a -> t^(+-1) a, t -> t a^(+-1), t -> a^(+-1) t of F(a,t),
through cyclically reduced words of length <= LMAX. Every image presents the
same group as its source, but its presentation complex, and hence the
certificate search of vfib.py, differs. Prints `IMG source image length` for
each image class other than the source's (classes: cyclic rotation, inversion,
a -> A, t -> T).
"""
import sys

INV = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}


def inverse(w):
    return ''.join(INV[c] for c in reversed(w))


def canon(w):
    out = []
    for fa in (False, True):
        for ft in (False, True):
            u = ''.join(INV[c] if (fa and c in 'aA') or (ft and c in 'tT') else c for c in w)
            for v in (u, inverse(u)):
                out += [v[i:] + v[:i] for i in range(len(v))]
    return min(out)


def reduce_cyclic(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    while len(out) > 1 and out[0] == INV[out[-1]]:
        out = out[1:-1]
    return ''.join(out)


def moves(w):
    for g, h in (('a', 't'), ('t', 'a')):
        for s in (h, INV[h]):
            for right in (True, False):
                img = {g: g + s if right else s + g}
                img[INV[g]] = inverse(img[g])
                yield reduce_cyclic(''.join(img.get(c, c) for c in w))


def main():
    lmax = int(sys.argv[1])
    for w0 in sys.argv[2:]:
        c0 = canon(w0)
        seen, frontier = {c0: w0}, [w0]
        while frontier:
            nxt = []
            for w in frontier:
                for u in moves(w):
                    if len(u) <= lmax:
                        cu = canon(u)
                        if cu not in seen:
                            seen[cu] = u
                            nxt.append(u)
            frontier = nxt
        for cu, u in sorted(seen.items(), key=lambda x: (len(x[1]), x[0])):
            if cu != c0:
                print('IMG', w0, cu, len(cu))
    print('SENTINEL_DONE')


if __name__ == '__main__':
    main()
