#!/usr/bin/env python3
"""Exhaustive length-bounded Andrews-Curtis orbit search in F_2 whose TARGET is any
thickenable presentation (Neuwirth test, libthick.so), not the standard basis.

Justification of the target: Lackenby (arXiv 2606.06122, Thm 1.3, completing Guo) --
a thickenable balanced presentation of the trivial group is AC-trivial.  So if the
AC orbit of AK(3) = <x,y | xyxYXY, xxxYYYY> contains a thickenable presentation,
AK(3) is AC-trivial.

States: unordered pairs of cyclic words (conjugacy classes up to inversion), further
quotiented by the 8 signed permutations of {x,y} (these are automorphisms of F_2 that
are homeomorphisms of the presentation complex, so both AC-triviality and
thickenability are invariant).
Moves: r_i -> cyclic reduction of (rotation of r_i)(rotation of r_j^{+-1}); every such
move is a composite of AC moves.  Optional --aut: also apply the elementary Nielsen
automorphisms x->xy, x->yx (and the symmetric ones) to both relators; automorphisms
map AC classes to AC classes and fix the class of the basis, so this is sound for the
question "is AK(3) AC-trivial".
Usage: acthick.py r1 r2 LMAX [maxstates] [--aut] [--basis|--knot|--both] [--per]
  --knot: exact torus-knot meridian target of meridian.py (sufficient for AC-triviality);
  --both: thickenable OR meridian target.
  LMAX bounds the total length, or with --per the length of each relator.
Output: first thickenable state with its path, or the exhaustive count.
"""
import sys, time
from collections import deque
import thickc
import meridian

def red(w):
    s = []
    for c in w:
        if s and s[-1] == c.swapcase():
            s.pop()
        else:
            s.append(c)
    return ''.join(s)

def cred(w):
    w = red(w)
    i, j = 0, len(w)
    while j - i >= 2 and w[i] == w[j - 1].swapcase():
        i += 1; j -= 1
    return w[i:j]

def inv(w):
    return w[::-1].swapcase()

SYMS = []
for sw in (False, True):
    for sx in (False, True):
        for sy in (False, True):
            m = {}
            for a, A, flip in (('x', 'X', sx), ('y', 'Y', sy)):
                b, B = (('y', 'Y') if a == 'x' else ('x', 'X')) if sw else (a, A)
                if flip:
                    b, B = B, b
                m[a], m[A] = b, B
            SYMS.append(str.maketrans(m))

def ccanon(w):
    if not w:
        return w
    best = None
    for v in (w, inv(w)):
        for i in range(len(v)):
            r = v[i:] + v[:i]
            if best is None or r < best:
                best = r
    return best

def canon(a, b):
    best = None
    for t in SYMS:
        p, q = ccanon(a.translate(t)), ccanon(b.translate(t))
        s = (p, q) if p <= q else (q, p)
        if best is None or s < best:
            best = s
    return best

def rots(w):
    return [w[i:] + w[:i] for i in range(len(w))] or ['']

def aut_images(a, b):
    outs = []
    for img in ('xy', 'yx', 'xY', 'Yx'):
        m = {'x': img, 'X': inv(img), 'y': 'y', 'Y': 'Y'}
        outs.append((cred(''.join(m[c] for c in a)), cred(''.join(m[c] for c in b))))
    return outs

def is_target(st, target):
    if target == 'basis':
        return len(st[0]) + len(st[1]) == 2
    if target in ('thick', 'both') and thickc.thick2(list(st)):
        return True
    if target in ('knot', 'both') and meridian.knot_target(st[0], st[1]):
        return True
    return False

def search(r1, r2, LMAX, maxstates=10**7, aut=False, log=sys.stdout, target='thick', per=False):
    ok = (lambda c, d: max(len(c), len(d)) <= LMAX) if per else (lambda c, d: len(c) + len(d) <= LMAX)
    start = canon(cred(r1), cred(r2))
    parent = {start: None}
    dq = deque([start])
    nthick_calls = 0; t0 = time.time()
    def found(s):
        path = []
        while s is not None:
            path.append(s); s = parent[s]
        return path[::-1]
    if is_target(start, target):
        return 'THICK', found(start), len(parent)
    while dq:
        s = dq.popleft()
        a, b = s
        cands = []
        for p, q in ((a, b), (b, a)):
            rq = rots(q) + rots(inv(q))
            for pr in rots(p):
                for qr in rq:
                    c = cred(pr + qr)
                    if c and ok(c, q):
                        cands.append((c, q))
        if aut:
            for (c, d) in aut_images(a, b) + aut_images(b.translate(SYMS[4]), a.translate(SYMS[4])):
                if c and d and ok(c, d):
                    cands.append((c, d))
        for c, d in cands:
            ns = canon(c, d)
            if ns in parent:
                continue
            parent[ns] = s
            nthick_calls += 1
            if is_target(ns, target):
                return 'THICK', found(ns), len(parent)
            dq.append(ns)
            if len(parent) >= maxstates:
                return 'CAPPED', None, len(parent)
    return 'EXHAUSTED', None, len(parent)

if __name__ == "__main__":
    args = [x for x in sys.argv[1:] if not x.startswith('--')]
    aut = '--aut' in sys.argv
    target = 'basis' if '--basis' in sys.argv else ('both' if '--both' in sys.argv else ('knot' if '--knot' in sys.argv else 'thick'))
    per = '--per' in sys.argv
    r1, r2, L = args[0], args[1], int(args[2])
    ms = int(args[3]) if len(args) > 3 else 10**7
    t0 = time.time()
    st, path, n = search(r1, r2, L, ms, aut, target=target, per=per)
    print("(%s,%s) LMAX=%d per=%s aut=%s target=%s: %s, %d states, %.1fs" % (r1, r2, L, per, aut, target, st, n, time.time() - t0))
    if path:
        for s in path:
            print("   ", s[0], "|", s[1])
    sys.stdout.flush()
