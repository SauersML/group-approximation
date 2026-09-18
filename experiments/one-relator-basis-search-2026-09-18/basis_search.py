"""Basis search for free Magnus pieces of G = <a,t | w>.

For a two-generator relator w, run a breadth-first search over relators w' = alpha(w), alpha a
product of elementary Nielsen automorphisms of F(a,t) (x -> xy^{+-1}, x -> y^{+-1}x), keeping
cyclically reduced words up to length LMAX.  G' = <a,t | w'> is isomorphic to G.  Whenever w' has
a letter s of exponent sum 0, rewrite w' by Magnus along s (letters x_i = s^-i x s^i), get the
piece W_0(x_0..x_n), and Whitehead-minimise it in F(x_0..x_n) while tracking the automorphism.
If W_0 is primitive, the piece B_0 is free of rank n and
    G = B_0 *_psi,  A = <x_0..x_(n-1)>,  B = <x_1..x_n>,  psi(x_i) = x_(i+1),
and lintongraph.certify (Linton, One-relator hierarchies, Thm 6.14/7.1, via the landed
soundness node linton-graph-certificate-soundness-proof) is run on it.  PASS means G is
hyperbolic and virtually special, hence residually finite and sofic.

Usage: basis_search.py LMAX FILE   (FILE: one relator per line, letters a,A,t,T; first field)
"""
import sys
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/one-relator-linton-graph-certificates-scripts')
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import lintongraph as LG
from whitehead import fr, cr, wh_auts
from collections import deque

CH = {'a': 1, 'A': -1, 't': 2, 'T': -2}
OUT = {1: 'a', -1: 'A', 2: 't', -2: 'T'}


def canon(w):
    """canonical representative of the cyclic word up to rotation and inversion."""
    w = tuple(w)
    inv = tuple(-x for x in reversed(w))
    return min(min(v[i:] + v[:i] for i in range(len(v))) for v in (w, inv))


def subst(w, img):
    o = []
    for x in w:
        o.extend(img[x] if x > 0 else [-z for z in reversed(img[-x])])
    return cr(o)


def nielsen():
    """elementary Nielsen automorphisms of F(1,2) as substitution dicts."""
    L = []
    for x, y in ((1, 2), (2, 1)):
        for e in (1, -1):
            L.append({x: [x, e * y], y: [y]})
            L.append({x: [e * y, x], y: [y]})
    return L


def app_wh(w, a, S, cyc):
    o = []
    for x in w:
        if x in (a, -a):
            o.append(x)
            continue
        o.extend(([-a] if (-x) in S else []) + [x] + ([a] if x in S else []))
    return cr(o) if cyc else fr(o)


def whmin_track(W, r):
    w = cr(W)
    img = {g: [g] for g in range(1, r + 1)}
    auts = list(wh_auts(r))
    imp = True
    while imp:
        imp = False
        for a, S in auts:
            v = app_wh(w, a, S, True)
            if len(v) < len(w):
                w = v
                img = {g: app_wh(img[g], a, S, False) for g in img}
                imp = True
                break
    return w, img


def magnus(w, s):
    """Magnus piece of cyclic w along letter s (exponent sum 0). Returns (n, W0) with letters
    1..n+1 standing for x_0..x_n, or None if the other letter does not occur."""
    x = 3 - s
    h, pairs = 0, []
    for c in w:
        if abs(c) == s:
            h += 1 if c > 0 else -1
        else:
            pairs.append((h, 1 if c > 0 else -1))
    assert h == 0
    if not pairs:
        return None
    m = min(p[0] for p in pairs)
    n = max(p[0] for p in pairs) - m
    return n, cr([sg * (p - m + 1) for p, sg in pairs])


def test_piece(n, W0):
    r = n + 1
    m, img = whmin_track(W0, r)
    if len(m) != 1:
        return 'NONFREE', len(m), None
    c = abs(m[0])
    others = [g for g in range(1, r + 1) if g != c]
    rel = {g: i + 1 for i, g in enumerate(others)}
    im = {g: tuple(fr([(rel[abs(z)] if z > 0 else -rel[abs(z)]) for z in img[g] if abs(z) != c]))
          for g in img}
    if n == 0:
        return 'TRIVIAL', 1, None
    A = [im[i] for i in range(1, n + 1)]
    B = [im[i] for i in range(2, n + 2)]
    v, info = LG.certify(n, A, B)
    return v, 1, (info, im)


def search(w0, LMAX, budget=200000):
    start = canon(cr(w0))
    seen = {start}
    Q = deque([start])
    N = nielsen()
    best = None
    tried = 0
    while Q and tried < budget:
        w = Q.popleft()
        tried += 1
        for s in (1, 2):
            if sum(1 if c == s else -1 if c == -s else 0 for c in w) != 0:
                continue
            mp = magnus(w, s)
            if mp is None:
                continue
            n, W0 = mp
            v, ml, rest = test_piece(n, W0)
            if rest is not None:
                info, im = rest
                if v.startswith('PASS'):
                    return ('PASS', w, s, n, W0, v, info, im, tried)
                if best is None:
                    best = ('FREEPIECE-FAIL', w, s, n, W0, v, info, im, tried)
        for img in N:
            v = canon(subst(w, img))
            if len(v) <= LMAX and v not in seen:
                seen.add(v)
                Q.append(v)
    return best or ('NOFREE', None, None, None, None, None, None, None, tried)


def ws(w):
    return ''.join(OUT[c] for c in w)


if __name__ == '__main__':
    LMAX = int(sys.argv[1])
    for line in open(sys.argv[2]):
        f = line.split()
        if not f:
            continue
        rel = f[-1] if f[0] == 'REST' else f[0]
        w = [CH[c] for c in rel]
        res = search(w, LMAX)
        tag = res[0]
        if res[1] is None:
            print('BASIS %s -> %s (states %d, LMAX %d)' % (rel, tag, res[8], LMAX), flush=True)
            continue
        _, wp, s, n, W0, v, info, im, tried = res
        print('BASIS %s -> %s via w\'=%s stable=%s n=%d W0=%s sZ=%s |V|=%d H=%s t=%s hloops=%s tloops=%s cycle=%s verdict=%s states=%d' % (
            rel, tag, ws(wp), OUT[s], n, '.'.join(('x%d' % (z - 1)) if z > 0 else ('X%d' % (-z - 1)) for z in W0),
            info.get('sZ'), len(info.get('V', [])), info.get('H'), info.get('t'), info.get('hloops'),
            info.get('tloops'), bool(info.get('cycle')), v, tried), flush=True)
    print('SENTINEL_DONE')
