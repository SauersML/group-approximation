#!/usr/bin/env python3
"""Magnus pieces of the 141 NONFREE length-16 residue classes.

For each word listed as NONFREE in lg_words16.out, and for each zero-exponent basis
that lintongraph.py tries (the unique character when the exponent sums are not both 0,
census.small_phis() otherwise), compute the Magnus piece W_0 as a cyclic word in the
letters a_m, ..., a_n (coded 1..k), and decide whether W_0 is primitive in F(k) by the
full Whitehead algorithm (greedy descent over all type-II Whitehead automorphisms of
F(k); by Whitehead's theorem a non-minimal cyclic word admits a strictly length-reducing
one, so the descent ends at a minimal-length representative, which has length 1 iff
W_0 is primitive).

Usage: pieces.py LG_WORDS16_OUT
"""
import sys, os, math, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'research/artifacts/or-unpeelable-census-scripts-2026-09-12'))
import census as C


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def cyc_reduce(w):
    w = free_reduce(w)
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1; j -= 1
    return w[i:j + 1]


def inv(w):
    return [-x for x in reversed(w)]


def apply(img, w, cyclic=False):
    out = []
    for x in w:
        out.extend(img[x] if x > 0 else inv(img[-x]))
    return cyc_reduce(out) if cyclic else free_reduce(out)


def whitehead_autos(k):
    """All type-II Whitehead automorphisms of F(k) (letters 1..k): multiplier a in +-1..+-k,
    each generator x != |a| goes to x, x a, a^-1 x or a^-1 x a; a goes to a."""
    autos = []
    for A in range(1, k + 1):
        for s in (1, -1):
            a = s * A
            others = [x for x in range(1, k + 1) if x != A]
            for choice in itertools.product(range(4), repeat=len(others)):
                if all(c == 0 for c in choice):
                    continue
                img = {A: [A]}
                for x, c in zip(others, choice):
                    img[x] = [[x], [x, a], [-a, x], [-a, x, a]][c]
                autos.append(img)
    return autos


_AUT = {}


def wh_descend(w, k):
    """Greedy Whitehead descent. Returns (minimal cyclic word, phi) with phi(original) conjugate
    to the minimal word, phi given as images of 1..k."""
    if k not in _AUT:
        _AUT[k] = whitehead_autos(k)
    phi = {x: [x] for x in range(1, k + 1)}
    w = cyc_reduce(w)
    improved = True
    while improved and len(w) > 1:
        improved = False
        for img in _AUT[k]:
            v = apply(img, w, cyclic=True)
            if len(v) < len(w):
                w = v
                phi = {x: apply(img, phi[x]) for x in phi}
                improved = True
                break
    return w, phi


def piece(cs):
    """(levels, gcd, W_0 coded 1..k) for a canonical Magnus sequence."""
    m, n, g, top, bot = C.extremes(cs)
    letters = list(range(m, n + 1, g)) if g else [m]
    code = {h: i + 1 for i, h in enumerate(letters)}
    W = []
    for h, e in cs:
        W.extend(C.power(code[h], e))
    return letters, g, cyc_reduce(W)


def phis_for(w):
    p, q = C.expsums(w)
    if (p, q) != (0, 0):
        g = math.gcd(p, q)
        return [(q // g, -p // g)]
    return C.small_phis()


def wstr(W):
    return '.'.join(('a%d' % (x - 1)) if x > 0 else ('A%d' % (-x - 1)) for x in W)


def main():
    code = {'a': 1, 'A': -1, 't': 2, 'T': -2}
    words = []
    for line in open(sys.argv[1]):
        f = line.split()
        if len(f) >= 6 and f[0] == 'VERDICT' and f[-1] == 'NONFREE':
            words.append(f[2])
    print('NONFREE words: %d' % len(words), flush=True)
    for wtxt in words:
        w = [code[ch] for ch in wtxt]
        for (x, y) in phis_for(w):
            seq = C.magnus(C.adapt(list(w), x, y))
            if seq is None:
                print('PIECE %s phi=%d,%d NOSEQ' % (wtxt, x, y)); continue
            cs = list(C.canon(seq))
            letters, g, W = piece(cs)
            k = len(letters)
            m, n, g2, top, bot = C.extremes(cs)
            peel = C.peelable(top) or C.peelable(bot)
            Wm, phi = wh_descend(W, k)
            print('PIECE %s phi=%d,%d levels=%d g=%d peel=%s |W0|=%d W0=%s whmin=%d %s'
                  % (wtxt, x, y, k, g, peel, len(W), wstr(W), len(Wm),
                     'PRIMITIVE' if len(Wm) == 1 else 'NONPRIM'), flush=True)
    print('SENTINEL_DONE', flush=True)


if __name__ == '__main__':
    main()
