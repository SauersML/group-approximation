"""Specific-form test (A_3 arc model of the I2(5) single-flat shadow).

Pure single-edge hexagon data a1, a2 in F = <A24, A34>, b1 in N = <A12, A13>; x1 = gamma0, x2 = a1.gamma0,
x3 = a1 b1 a2.gamma0, y2 = a1 b1.delta0.  The Huang-type forms asked for in the brief are
  (Y2)  y2 is adjacent to x1  (i(y2, x1) = 0), or
  (TW)  sigma1^m.delta0 (the analogue of s4^k A_Y; sigma1^2 = A12 plays s4^2) is adjacent to x2 and x3.
Both are curver intersection-number checks.  Only when both fail do we run the (slow) placement test that
the 6-cycle closes (q in the d1-face of x1 u x3); such a hexagon answers the brief's question with NO.
Run: PYTHONPATH=.:<curver>:<realalg> python3 spec.py [L] [lo] [hi] [M]"""
import sys, itertools
from search import S, X0, cvarc
from search2 import words, outer, A24, A34, A12, A13

sys.setrecursionlimit(20000)
Y0 = S.arcs['s_0']
_cy = {}


def cy(braid):
    k = tuple(braid)
    if k not in _cy:
        h = S('.'.join(('s_%d' if g > 0 else 'S_%d') % abs(g) for g in braid)) if braid else S('')
        _cy[k] = h(Y0)
    return _cy[k]


def main(L=2, lo=0, hi=None, M=8):
    FA = words([A24, A34], L)
    NB = words([A12, A13], L)
    tw = {m: cy([1] * m if m >= 0 else [-1] * (-m)) for m in range(-M, M + 1)}
    x1 = cvarc([])
    n = y2ok = twok = both = fail = closing_fail = undet = 0
    for (wa1, a1), (wb1, b1), (wa2, a2) in itertools.product(FA[lo:hi], NB, FA):
        x2, x3 = cvarc(a1), cvarc(a1 + b1 + a2)
        if x3 == x1 or x3 == x2:
            continue
        n += 1
        f1 = cy(a1 + b1).intersection(x1) == 0
        ms = [m for m, d in tw.items() if d.intersection(x2) == 0 and d.intersection(x3) == 0]
        y2ok += f1
        twok += bool(ms)
        both += f1 and bool(ms)
        if f1 or ms:
            continue
        fail += 1
        s13 = outer([[], a1 + b1 + a2])
        if s13 is None:
            undet += 1
            continue
        if s13 != 'dup' and 0 in s13:
            closing_fail += 1
            print('NOFORM closing hexagon a1', wa1, 'b1', wb1, 'a2', wa2, flush=True)
    print('hexagon data', n, 'y2~x1', y2ok, 'twist centre', twok, 'both', both, 'neither', fail,
          'neither+closing', closing_fail, 'undetermined', undet)


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
