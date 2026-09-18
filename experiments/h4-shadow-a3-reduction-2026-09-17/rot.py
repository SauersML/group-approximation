"""Rotation-invariant specific-form test on the spec.py NOFORM closing A_3 hexagons.

For each (a1, b1, a2) from spec_L2*.log: find b3 (findb3), set a3 = (a1a2)^-1, b2 = b1^-1 b3^-1, and test
  (V)  some y_i is adjacent to all of x1, x2, x3;
  (E)  for some hexagon edge (x_i, y) with transport g (g.(A_X, A_Y) = (x_i, y)) and |j| <= M,
       g A12^j A_Y is adjacent to x1, x2, x3   [the form s4^{2j}A_Y read from every base edge].
Transports: (x1,y1) 1, (x2,y1) a1, (x2,y2) a1b1, (x3,y2) a1b1a2, (x3,y3) b3^-1 a3^-1, (x1,y3) b3^-1.
Run: PYTHONPATH=.:<curver>:<realalg> python3 rot.py [M] [LN3]"""
import sys, re, ast
from search import cvarc
from search2 import words, inv, A24, A34, A12, A13
from spec import cy
from tuples import sig, mc
from findb3 import ev, FG, NG

sys.setrecursionlimit(20000)


def cases():
    out = []
    for f in ('spec_L2a.log', 'spec_L2b.log'):
        for line in open(f):
            m = re.match(r'NOFORM closing hexagon a1 (.*) b1 (.*) a2 (.*)$', line.strip())
            if m:
                out.append(tuple(ast.literal_eval(g) for g in m.groups()))
    return out


def centre(braid, X):
    y = cy(braid)
    return all(y.intersection(x) == 0 for x in X)


def main(M=6, LN3=5):
    NB = [((), [])] + words(NG, LN3)
    tot = surv = 0
    for wa1, wb1, wa2 in cases():
        a1, b1, a2 = ev(wa1, FG), ev(wb1, NG), ev(wa2, FG)
        target = sig(a1 + b1 + a2 + inv(b1))
        b3s = [(w, b) for w, b in NB if sig(inv(b) + a1 + a2 + b) == target
               and mc(inv(b) + a1 + a2 + b) == mc(a1 + b1 + a2 + inv(b1))]
        if not b3s:
            print('no b3 found', wa1, wb1, wa2)
            continue
        wb3, b3 = b3s[0]
        a3 = inv(a1 + a2)
        X = [cvarc([]), cvarc(a1), cvarc(a1 + b1 + a2)]
        V = [i for i, g in enumerate([[], a1 + b1, inv(b3)]) if centre(g, X)]
        E = []
        for name, g in [('x1y1', []), ('x2y1', a1), ('x2y2', a1 + b1), ('x3y2', a1 + b1 + a2),
                        ('x3y3', inv(b3) + inv(a3)), ('x1y3', inv(b3))]:
            for j in range(-M, M + 1):
                if j and centre(g + (A12 * j if j > 0 else inv(A12) * (-j)), X):
                    E.append((name, j))
        tot += 1
        ok = bool(V or E)
        surv += not ok
        print('a1', wa1, 'b1', wb1, 'a2', wa2, 'b3', wb3, '| vertex centres y', [i + 1 for i in V],
              '| edge-twist centres', E[:6], '' if ok else '<-- NO FORM IN ANY ROTATION', flush=True)
    print('hexagons', tot, 'with no rotation-invariant form', surv)


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
