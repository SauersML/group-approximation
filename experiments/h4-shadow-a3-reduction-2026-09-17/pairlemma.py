"""Test the pair lemma in the A_3 arc model: for arcs x1,x2,x3 from t to d0 and a puncture p in {q,a,b},
   p in the d1-region of every x_i u x_j  ==>  p in the d1-region of x1 u x2 u x3 ?
Run: PYTHONPATH=.:<curver>:<realalg> python3 pairlemma.py [nbraids] [maxlen] [seed]"""
import sys, itertools
from arcs import Arc
from search import outer, gen

sys.setrecursionlimit(20000)


def main(n=31, L=6, seed=1):
    g0 = Arc('d0', (), ('P', 3))
    arcs = [([], g0)] + gen(n, L, seed)
    m = len(arcs)
    pair = {}
    for i, j in itertools.combinations(range(m), 2):
        pair[(i, j)] = outer([arcs[i], arcs[j]])
    tested = bad = undet = 0
    for i, j, k in itertools.combinations(range(m), 3):
        ps = [pair[(i, j)], pair[(i, k)], pair[(j, k)]]
        if any(s is None for s in ps):
            undet += 1
            continue
        common = ps[0] & ps[1] & ps[2]
        if not common:
            continue
        s = outer([arcs[i], arcs[j], arcs[k]])
        if s is None:
            undet += 1
            continue
        tested += 1
        if not common <= s:
            bad += 1
            print('VIOLATION', [arcs[x][0] for x in (i, j, k)], 'pairs', [sorted(p) for p in ps], 'triple', sorted(s),
                  flush=True)
    print('triples with a common pair-outer puncture', tested, 'violations', bad, 'undetermined', undet)


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    main(*a)
