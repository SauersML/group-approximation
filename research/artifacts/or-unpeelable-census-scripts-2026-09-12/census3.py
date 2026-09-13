#!/usr/bin/env python3
"""Full census of two-generator one-relator relators of length L.

Every cyclically reduced w in F(a,t) of length L, up to rotation, signed
permutation of the letters and reversal (all of which preserve the group up to
isomorphism).  Classes are sorted into: PP (some letter occurs with one sign),
POWER (proper power: torsion, handled by Wise), and otherwise census.cert_word.
Uncertified classes get the breadth-first partial-positivity search of
census2.pp_search.  Usage: census3.py LMIN LMAX MAXPRINT
"""
import sys, time
from collections import Counter
import census as C
import census2 as C2

MAPS = []
for sw in (False, True):
    for sa in (1, -1):
        for st in (1, -1):
            def f(x, sw=sw, sa=sa, st=st):
                s = 1 if x > 0 else -1
                ab = abs(x)
                if sw:
                    ab = 3 - ab
                return s * ab * (sa if ab == 1 else st)
            MAPS.append(f)

def is_canon(w):
    L = len(w)
    t = tuple(w)
    for f in MAPS:
        img = [f(x) for x in w]
        for v in (img, img[::-1]):
            v = tuple(v)
            for r in range(L):
                u = v[r:] + v[:r]
                if u < t:
                    return False
    return True

def words(L):
    w = [-2]
    def rec():
        if len(w) == L:
            if w[-1] != -w[0]:
                yield w
            return
        for x in (-2, -1, 1, 2):
            if x != -w[-1]:
                w.append(x)
                yield from rec()
                w.pop()
    yield from rec()

def main():
    lmin, lmax, maxprint = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for L in range(lmin, lmax + 1):
        t0 = time.time()
        cats, surv, nclass = Counter(), [], 0
        for w in words(L):
            if C.pp(w):
                continue
            if not is_canon(w):
                continue
            nclass += 1
            w = list(w)
            if C.min_period(w) < L:
                cats['POWER'] += 1
                continue
            C.BUDGET[0] = 3000
            ok, why = C.cert_word(w, 0)
            if ok:
                cats[why.split('[')[0]] += 1
            else:
                cats['SURVIVOR'] += 1
                surv.append(w)
        zero = Counter(0 in C.expsums(w) for w in surv)
        rest = [w for w in surv if C2.pp_search(w, 4, 20000) is None]
        print('L=%d nonPP_classes=%d time=%.0fs cats=%s' % (L, nclass, time.time() - t0, sorted(cats.items())), flush=True)
        print(' survivors=%d with_zero_expsum=%s pp_bfs_remaining=%d' % (len(surv), sorted(zero.items()), len(rest)), flush=True)
        for w in rest[:maxprint]:
            p, q = C.expsums(w)
            print('  REST %s expsums=(%d,%d)' % (C.word_str(w), p, q))
        print('DONE_L=%d' % L, flush=True)
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
