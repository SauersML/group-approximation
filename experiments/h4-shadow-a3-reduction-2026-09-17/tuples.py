"""Exact normal-form tuples in the A_3 model and the specific-form test.

Tuple: a1, a2, a3 in F = <A24, A34>, b1, b2, b3 in N = <A12, A13> with a1a2a3 = 1, b1b2b3 = 1,
a1 b1 a2 b2 a3 b3 = 1 in P_4.  Put a3 = (a1a2)^-1, b2 = b1^-1 b3^-1; the remaining condition is
    b3^-1 (a1 a2) b3 = a1 b1 a2 b1^-1          (*)
checked in the mapping class group (curver), hashed by images of the arc chain, then confirmed by ==.
For each nondegenerate solution (all a_i, b_i != 1) test the forms of the brief:
  Y2 : i(y2, x1) = 0,  y2 = a1 b1 . delta0
  TWe: i(A12^j . delta0, x2) = i(A12^j . delta0, x3) = 0 for some |j| <= M   (A12 = sigma1^2 <-> s4^2)
  TWo: the same with sigma1^m, m odd, |m| <= 2M+1   (no shadow meaning; reported for completeness)
and whether some centre exists at all (q in the d1-face of x1 u x2 u x3, placement test).
Run: PYTHONPATH=.:<curver>:<realalg> python3 tuples.py [LF] [LN] [M]"""
import sys, itertools
from search import S, cvarc
from search2 import words, outer, inv, A24, A34, A12, A13
from spec import cy

sys.setrecursionlimit(20000)
CHAIN = [S.arcs[k] for k in sorted(S.arcs)]


def mc(braid):
    return S('.'.join(('s_%d' if g > 0 else 'S_%d') % abs(g) for g in braid)) if braid else S('')


def sig(braid):
    h = mc(braid)
    return tuple(tuple(h(a).geometric) for a in CHAIN)


def main(LF=2, LN=2, M=6):
    FA = words([A24, A34], LF)
    NB = words([A12, A13], LN)
    lhs = {}
    for (wa1, a1), (wa2, a2) in itertools.product(FA, FA):
        for wb3, b3 in NB:
            lhs.setdefault(sig(inv(b3) + a1 + a2 + b3), []).append((wa1, wa2, wb3, b3))
    x1 = cvarc([])
    twe = {j: cy(A12 * j if j >= 0 else inv(A12) * (-j)) for j in range(-M, M + 1)}
    two = {m: cy([1] * m if m > 0 else [-1] * (-m)) for m in range(-2 * M - 1, 2 * M + 2, 2)}
    sols = noform = 0
    from collections import Counter
    stat = Counter()
    for (wa1, a1), (wb1, b1), (wa2, a2) in itertools.product(FA, NB, FA):
        rhs = a1 + b1 + a2 + inv(b1)
        for (va1, va2, wb3, b3) in lhs.get(sig(rhs), []):
            if (va1, va2) != (wa1, wa2) or mc(inv(b3) + a1 + a2 + b3) != mc(rhs):
                continue
            b2 = inv(b1) + inv(b3)
            if mc(a1 + a2).is_identity() or mc(b2).is_identity():
                continue
            sols += 1
            x2, x3 = cvarc(a1), cvarc(a1 + b1 + a2)
            y2 = cy(a1 + b1).intersection(x1) == 0
            je = [j for j, d in twe.items() if d.intersection(x2) == 0 and d.intersection(x3) == 0]
            mo = [m for m, d in two.items() if d.intersection(x2) == 0 and d.intersection(x3) == 0]
            stat[(bool(y2), tuple(je))] += 1
            if y2 or je:
                continue
            noform += 1
            s = outer([[], a1, a1 + b1 + a2])
            print('NOFORM a1', wa1, 'b1', wb1, 'a2', wa2, 'b3', wb3, '| odd-twist centres', mo,
                  '| triple d1-face', s if s in (None, 'dup') else sorted(s), flush=True)
    for k, v in sorted(stat.items()):
        print('  y2~x1', k[0], 'twist j', list(k[1]), ':', v)
    print('nondegenerate tuples', sols, 'with no centre of form y2 or A12^j.y1', noform)


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
