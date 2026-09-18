"""Alternating search for window-B_2 Ramsey witnesses in Thompson's F.

Start from the transplanted cone E = {g : some geodesic of g starts with x1^{+-1}} and alternate
  (i) LP: best lambda on ordered pairs of B_2 for the current E, and
  (ii) MILP: best E subset B_n for the current lambda (maximize the minimum over x in I_n),
recording every (E, lambda) whose value, recomputed exactly in Fractions, exceeds 1/2.
A certified value > 1/2 at radius n proves R_{F,S}(2) > n (dual form, see window2.py).

Usage: python3 alternate.py N_MIN N_MAX ROUNDS TIME_LIMIT_SECONDS
"""
import json
import sys
from fractions import Fraction as Q

import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

from window2 import window_words, solve_lp, exact_value, F_ID, F_GENS, f_mul, ball


def setup(N):
    dist = ball(F_GENS, F_ID, f_mul, N)
    left = [{} for _ in F_GENS]
    for i, s in enumerate(F_GENS):
        for x in dist:
            y = f_mul(s, x)
            if y in dist:
                left[i][x] = y
    words = [w for _, w in window_words(F_GENS, F_ID, f_mul)]

    def act(word, x):
        for i in reversed(word):
            x = left[i].get(x)
            if x is None:
                return None
        return x
    inv_idx = [1, 0, 3, 2]
    first = {g: frozenset(i for i in range(4) if d > 0 and
                          dist.get(left[inv_idx[i]].get(g), -9) == d - 1) for g, d in dist.items()}
    geo = {F_ID: ()}  # a geodesic word (generator indices, leftmost first) for each element
    for g, d in sorted(dist.items(), key=lambda t: t[1]):
        if d:
            i = min(first[g])
            geo[g] = (i,) + geo[left[inv_idx[i]][g]]
    return dist, words, act, first, geo


def run(n, dist, words, act, first, geo, rounds, tl):
    In = []
    for x, d in dist.items():
        if d <= n:
            imgs = [act(w, x) for w in words]
            if all(y is not None and dist[y] <= n for y in imgs):
                In.append(imgs)
    elems = sorted({y for imgs in In for y in imgs}, key=lambda g: (dist[g], str(g)))
    idx = {g: i for i, g in enumerate(elems)}
    E = {g for g in elems if first[g] & {2, 3}}
    best = None
    log = []
    k = len(words)
    for r in range(rounds):
        pics = [tuple(int(y in E) for y in imgs) for imgs in In]
        upics = sorted(set(pics))
        pairs, lam, lpval = solve_lp(upics, k)
        val, support = exact_value(pairs, lam, upics)
        log.append({'round': r, 'step': 'lp', 'value': str(val)})
        if best is None or val > best[0]:
            best = (val, sorted(idx[g] for g in E), support)
        # MILP for E given lam
        nv = len(elems) + 1
        A = lil_matrix((len(In), nv))
        for row, imgs in enumerate(In):
            for w, (a, b) in zip(lam, pairs):
                if w > 1e-12:
                    A[row, idx[imgs[a]]] += w
                    A[row, idx[imgs[b]]] -= w
            A[row, nv - 1] = -1.0
        c = np.zeros(nv)
        c[-1] = -1.0
        integrality = np.ones(nv)
        integrality[-1] = 0
        res = milp(c, constraints=LinearConstraint(A.tocsr(), lb=0, ub=np.inf),
                   integrality=integrality,
                   bounds=Bounds(np.r_[np.zeros(nv - 1), -2.0], np.r_[np.ones(nv - 1), 2.0]),
                   options={'time_limit': tl, 'disp': False})
        if res.x is None:
            log.append({'round': r, 'step': 'milp', 'status': res.message})
            break
        E = {g for g in elems if res.x[idx[g]] > 0.5}
        log.append({'round': r, 'step': 'milp', 'milp_value': float(-res.fun), 'status': res.message})
        print(json.dumps({'n': n, **log[-1]}), file=sys.stderr, flush=True)
    pics = sorted({tuple(int(y in E) for y in imgs) for imgs in In})
    pairs, lam, lpval = solve_lp(pics, k)
    val, support = exact_value(pairs, lam, pics)
    log.append({'round': rounds, 'step': 'final-lp', 'value': str(val)})
    if val > best[0]:
        best = (val, sorted(idx[g] for g in E), support)
    return {'n': n, '|I_n|': len(In), 'best_exact_value': str(best[0]),
            'certifies_R2_gt_n': best[0] > Q(1, 2), 'window_words': words, 'lambda': best[2],
            'E_size': len(best[1]), 'E_geodesic_words': sorted(geo[elems[i]] for i in best[1]),
            'log': log}


if __name__ == '__main__':
    n0, n1, rounds, tl = map(int, sys.argv[1:5])
    dist, words, act, first, geo = setup(n1)
    out = []
    for n in range(n0, n1 + 1):
        res = run(n, dist, words, act, first, geo, rounds, tl)
        out.append(res)
        print(json.dumps({k: v for k, v in res.items() if k not in ('log', 'E_geodesic_words')}),
              file=sys.stderr, flush=True)
    print(json.dumps(out, indent=1))
