#!/usr/bin/env python3
"""Batched free-by-cyclic / ascending-HNN target search for the (3,1,3) words.

For a (3,1,3) rewrite r' the middle letter occurs once, so r' = 1 says a_1 = V(a_0, a_2) for a
word V over {a_0, a_2} (read off by rotating r' to start at the a_1 letter).  A target is an
injective endomorphism psi of F(x, y) and g in F with
      psi(g) = V(g, psi^2 g)  freely,   [g, psi g] != 1;
then a -> g, t -> s maps G into the mapping torus <F, s | s^-1 w s = psi(w)> (free-by-cyclic,
or ascending HNN, so in H), injectively on the rank-2 edge group <a_0, a_1>, and G is in H by
the edge-injective quotient lemma.  Both orientations (V and its mirror a_0 <-> a_2) are tried.

Filter: in H_1(F) = Z^2, psi acts by an integer matrix M and ab(psi g) = e0*ab(g) + e2*ab(psi^2 g)
with (e0, e2) the exponent sums of V; only (psi, g) passing it are expanded.

Usage: fbc_batch.py WORDFILE LI LG     (images of psi of length <= LI, g of length <= LG)
Prints every hit 'word V psi(x) psi(y) g' and a summary of words with a hit.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.chdir(HERE)
from classify import rewrites  # noqa: E402


def red(w):
    out = []
    for c in w:
        if out and out[-1] == c.swapcase():
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def inv(w):
    return w[::-1].swapcase()


def words(n, L="xXyY"):
    res, layer = [], ['']
    for _ in range(n):
        layer = [w + c for w in layer for c in L if not (w and w[-1] == c.swapcase())]
        res += layer
    return res


def app(psi, w):
    return red(''.join(psi[c] if c.islower() else inv(psi[c.lower()]) for c in w))


def ab(w):
    return (w.count('x') - w.count('X'), w.count('y') - w.count('Y'))


def V_of(r):
    """a_1 = V(a_0, a_2) as a tuple of (p, e), p in {0, 2}."""
    i = next(j for j, ((_, p), _) in enumerate(r) if p == 1)
    eps = r[i][1]
    rest = r[i + 1:] + r[:i]          # r' = a_1^eps * rest  (cyclically)
    U = tuple((p, e) for (_, p), e in rest)
    if eps == 1:                      # a_1 = rest^-1
        return tuple((p, -e) for p, e in reversed(U))
    return U


def main():
    LI, LG = int(sys.argv[2]), int(sys.argv[3])
    table = {}                        # (e0, e2) -> list of (V, word)
    allw = open(sys.argv[1]).read().split()
    for s in allw:
        for r, ev, occ in rewrites(s):
            if occ != [3, 1, 3]:
                continue
            for mirror in (False, True):
                rr = tuple(((0, 2 - p if mirror else p), e) for (_, p), e in r)
                V = V_of(rr)
                e0 = sum(e for p, e in V if p == 0)
                e2 = sum(e for p, e in V if p == 2)
                table.setdefault((e0, e2), []).append((V, s, mirror))
    W = words(LI)
    G = words(LG)
    hits = {}
    for px in W:
        for py in W:
            if red(px + py + inv(px) + inv(py)) == '':
                continue
            psi = {'x': px, 'y': py}
            ax, ay = ab(px), ab(py)
            for g in G:
                a0 = ab(g)
                a1 = (a0[0] * ax[0] + a0[1] * ay[0], a0[0] * ax[1] + a0[1] * ay[1])
                a2 = (a1[0] * ax[0] + a1[1] * ay[0], a1[0] * ax[1] + a1[1] * ay[1])
                cand = [k for k in table
                        if a1 == (k[0] * a0[0] + k[1] * a2[0], k[0] * a0[1] + k[1] * a2[1])]
                if not cand:
                    continue
                g1 = app(psi, g)
                if red(g + g1 + inv(g) + inv(g1)) == '':
                    continue
                g2 = app(psi, g1)
                img = {0: (g, inv(g)), 2: (g2, inv(g2))}
                for k in cand:
                    for V, s, mirror in table[k]:
                        if s in hits:
                            continue
                        if red(''.join(img[p][0 if e == 1 else 1] for p, e in V)) == g1:
                            hits[s] = (V, mirror, px, py, g)
                            print("HIT", s, "mirror" if mirror else "direct", px, py, g)
                            sys.stdout.flush()
    print("# LI=%d LG=%d: %d of %d words hit" % (LI, LG, len(hits), len(allw)))


if __name__ == '__main__':
    main()
