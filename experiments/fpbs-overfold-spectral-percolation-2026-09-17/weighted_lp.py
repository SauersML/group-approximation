"""Weighted closure counting is also dead: an LP over atom-type weights.

Weighted Lemma 1: give type i weight w_i >= 0, w_lawful = 1.  Each closure
step uses a distinct full hyperedge h and activates an atom of weight at
most W(h) = max_{atoms of h} w, so w(C) - w(S) <= sum_{h full in C} W(h).
A lower bound on w(S) (hence on deep, since w(S) <= max(w)|S|) needs
sum_{h in A} W(h) <= w(A) - delta n for the sets A at some stage.

Test sets: A = B_r x I in the Cayley tree (r <= RMAX, I any set of types);
disjoint packings of such blocks exist in every level of large girth, at
every scale.  The LP
    minimise t  s.t.  sum_{k: types(k) in I} c_k(r) M_k - |B_r| w(I) <= t |B_r|,
                      M_k >= w_i (i in k),  w_lawful = 1,  w >= 0
has optimum t* > 0 iff every weighting admits a block with weighted
F exceeding weighted size (so the argument yields nothing).
Usage: python3 weighted_lp.py j RMAX
"""
import sys
import itertools
import numpy as np
from scipy.optimize import linprog
from hyper import build
from tree_count import words, mul


def counts(M, r):
    L = max(len(w) for ent in M['hyp'] for _, w in ent)
    pts = words(r + L)
    c = [0] * len(M['hyp'])
    for q in pts:
        for k, ent in enumerate(M['hyp']):
            if all(len(mul(q, w)) <= r for _, w in ent):
                c[k] += 1
    return c


def main():
    j, RMAX = int(sys.argv[1]), int(sys.argv[2])
    M = build(j)
    R, K = M['R'], len(M['hyp'])
    law = M['lawful'].index(True)
    types = [set(i for i, _ in ent) for ent in M['hyp']]
    C = {r: counts(M, r) for r in range(1, RMAX + 1)}
    size = {r: len(words(r)) for r in C}
    # variables: w_0..w_{R-1}, M_0..M_{K-1}, t
    nv = R + K + 1
    A_ub, b_ub = [], []
    for r in C:
        for m in range(1, R + 1):
            for I in itertools.combinations(range(R), m):
                I = set(I)
                row = np.zeros(nv)
                for k in range(K):
                    if types[k] <= I:
                        row[R + k] += C[r][k]
                for i in I:
                    row[i] -= size[r]
                row[-1] = -size[r]
                A_ub.append(row)
                b_ub.append(0.0)
    for k in range(K):
        for i in types[k]:
            row = np.zeros(nv)
            row[i] = 1
            row[R + k] = -1
            A_ub.append(row)
            b_ub.append(0.0)
    A_eq = np.zeros((1, nv))
    A_eq[0, law] = 1
    bounds = [(0, None)] * (R + K) + [(None, None)]
    obj = np.zeros(nv)
    obj[-1] = 1
    res = linprog(obj, A_ub=np.array(A_ub), b_ub=b_ub, A_eq=A_eq, b_eq=[1],
                  bounds=bounds, method='highs')
    print('j', j, 'RMAX', RMAX, 'types', R, 'triangle types', K,
          'constraints', len(A_ub))
    print('status', res.status, res.message)
    print('t* (per ball point) = %.6f' % res.fun)
    print('optimal weights w:', np.round(res.x[:R], 4))


if __name__ == '__main__':
    main()
