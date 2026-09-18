"""Independent exact check of the window-B_2 witnesses written by alternate.py.

For each record: rebuild B_n of F by BFS, rebuild E from its geodesic words (generator indices into
F_GENS = [x0, x0^-1, x1, x1^-1], leftmost letter first), rebuild the window B_2 from window_words
(word (i, j) is s_i s_j), recompute I_n = {x : B_2 x subset B_n}, and evaluate
  min_{x in I_n} sum lam(a,b) (1_E(a x) - 1_E(b x))
in Fraction arithmetic. A value > 1/2 proves that B_n is not 1/2-Ramsey w.r.t. B_2, i.e. R_{F,S}(2) > n.

Usage: python3 verify_witnesses.py alternate_F_B2_n7-10.json
"""
import json
import sys
from fractions import Fraction as Q

from window2 import F_ID, F_GENS, f_mul, ball


def elem(word):
    g = F_ID
    for i in reversed(word):
        g = f_mul(F_GENS[i], g)
    return g


def check(rec):
    n = rec['n']
    dist = ball(F_GENS, F_ID, f_mul, n)
    E = set()
    for w in rec['E_geodesic_words']:
        g = elem(w)
        assert dist.get(g, n + 1) <= n and dist[g] == len(w), 'E must lie in B_n, words geodesic'
        E.add(g)
    win = [elem(w) for w in rec['window_words']]
    lam = [(int(k.split('-')[0]), int(k.split('-')[1]), Q(v)) for k, v in rec['lambda'].items()]
    assert sum(v for _, _, v in lam) == 1 and all(v > 0 for _, _, v in lam)
    worst = None
    count = 0
    for x in dist:
        imgs = [f_mul(a, x) for a in win]
        if all(y in dist for y in imgs):
            count += 1
            val = sum(v * (int(imgs[a] in E) - int(imgs[b] in E)) for a, b, v in lam)
            worst = val if worst is None else min(worst, val)
    return {'n': n, '|I_n|': count, '|E|': len(E), 'exact_min': str(worst), 'R2_gt_n': worst > Q(1, 2)}


if __name__ == '__main__':
    for rec in json.load(open(sys.argv[1])):
        print(json.dumps(check(rec)), flush=True)
