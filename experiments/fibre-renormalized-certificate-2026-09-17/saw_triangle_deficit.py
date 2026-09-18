"""Rigorous lower bound on the percolation deficit D = d-1-1/p_c of
G_k = Cay(F_2, {a,b}^{+-1}) x Cay(Z, {+-1,...,+-k})  (Cartesian product).

p_c >= 1/mu >= 1/lambda, where lambda is the spectral radius of the transfer
matrix M on ordered label pairs (s,t), t != s^-1, forbidding the next label u
when u = t^-1 (backtrack) or s t u = e (triangle closure).  Every self-avoiding
walk has an admissible label sequence, so #SAW_n <= #admissible sequences and
mu <= lambda.  Collatz-Wielandt: lambda <= max_i (M v)_i / v_i for any positive
v; we round the float Perron vector to positive integers and evaluate the max
exactly with Fractions.  Output: exact upper bound on lambda (printed as float
after exact evaluation) and the resulting lower bound on D, compared with
delta_H = 4 - 2 sqrt 3 for the free-basis factor.

Usage: python3 saw_triangle_deficit.py 4 8 16 32
"""
import sys
import math
from fractions import Fraction

import numpy as np


def labels(k):
    H = [('a', 1), ('a', -1), ('b', 1), ('b', -1)]
    B = [('z', j) for j in range(1, k + 1)] + [('z', -j) for j in range(1, k + 1)]
    return H + B


def inv(s):
    return (s[0], -s[1])


def closes(s, t, u):
    # s t u = e in F_2 x Z (commuting factors): an H-letter has nontrivial
    # F_2-component unless paired with its inverse, and a pair leaves a lone
    # nonzero letter, so only all-Z triples can close.
    if s[0] == 'z' and t[0] == 'z' and u[0] == 'z':
        return s[1] + t[1] + u[1] == 0
    return False


def run(k, iters=600):
    L = labels(k)
    idx = {}
    states = []
    for s in L:
        for t in L:
            if t != inv(s):
                idx[(s, t)] = len(states)
                states.append((s, t))
    succ = []
    for (s, t) in states:
        succ.append([idx[(t, u)] for u in L if u != inv(t) and not closes(s, t, u)])
    rows = [np.array(r) for r in succ]
    v = np.ones(len(states))
    for _ in range(iters):
        w = np.array([v[r].sum() for r in rows])
        v = w / w.max()
    scale = 10 ** 12
    vi = [max(1, int(round(x * scale))) for x in v]
    best = Fraction(0)
    for i, r in enumerate(succ):
        q = Fraction(sum(vi[j] for j in r), vi[i])
        if q > best:
            best = q
    d = len(L)
    return d, best, (d - 1) - best


if __name__ == '__main__':
    ks = [int(x) for x in sys.argv[1:]] or [4, 8, 16, 32]
    deltaH = 4 - 2 * math.sqrt(3)
    print('delta_H (F_2 free basis) =', deltaH)
    for k in ks:
        d, lam, Dl = run(k)
        print(f'k={k:3d} d={d:3d} lambda <= {float(lam):.6f}  '
              f'D(G_k) >= {float(Dl):.6f}  exceeds delta_H: {Dl > Fraction(deltaH)}')
