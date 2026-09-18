"""For a closing A_3 hexagon (a1, b1, a2) with no centre of form y2 / sigma1^m.y1 (spec.py NOFORM), find
b3 in N = <A12, A13> with  b3^-1 (a1 a2) b3 = a1 b1 a2 b1^-1  (the exact tuple condition (*)).
Run: PYTHONPATH=.:<curver>:<realalg> python3 findb3.py [LN3]"""
import sys
from search2 import words, A24, A34, A12, A13, inv
from tuples import sig, mc

sys.setrecursionlimit(20000)
FG, NG = [A24, A34], [A12, A13]


def ev(w, gens):
    b = []
    for i, s in w:
        b += gens[i] if s == 1 else inv(gens[i])
    return b


CASES = [(((0, 1),), ((0, 1), (1, 1)), ((1, 1),)),
         (((0, 1),), ((0, 1), (1, -1)), ((1, 1),)),
         (((0, -1),), ((0, 1), (1, -1)), ((1, 1), (1, 1)))]


def main(LN3=6):
    NB = [([], [])] + words(NG, LN3)
    for wa1, wb1, wa2 in CASES:
        a1, b1, a2 = ev(wa1, FG), ev(wb1, NG), ev(wa2, FG)
        target = sig(a1 + b1 + a2 + inv(b1))
        hits = [wb3 for wb3, b3 in NB if sig(inv(b3) + a1 + a2 + b3) == target
                and mc(inv(b3) + a1 + a2 + b3) == mc(a1 + b1 + a2 + inv(b1))]
        print('a1', wa1, 'b1', wb1, 'a2', wa2, '-> b3', hits[:4], flush=True)


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
