"""Window-B_2 Ramsey witnesses in F_2 and in Thompson's F.

Dual form (Moore's definition, von Neumann minimax over the finite game):
  R(m) > n  iff  there are E subset B_n and a probability lam on ordered pairs (a, b) in B_m x B_m with
  sum lam(a,b) (1_E(a x) - 1_E(b x)) > 1/2 for every x in I_n = {x : B_m x subset B_n}.
The left side depends on x only through the picture X_E(x) = {a in B_m : a x in E}, so the LP has one
row per distinct picture.

Usage: python3 window2.py free        (F_2, all radii, via the length-3 prefix reduction)
       python3 window2.py thompson N  (F, radii 4..N, transplanted geodesic-first-letter sets)
Output: JSON on stdout. Every reported value is recomputed in exact Fraction arithmetic.
"""
import json
import sys
from fractions import Fraction as Q

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/ramsey-picture-sat-2026-09-17')
from groups import F_ID, F_GENS, f_mul, W_ID, W_GENS, w_mul, ball  # noqa: E402


def window_words(gens, ident, mul):
    """B_2 as a list of (element, word) with word a tuple of generator indices applied right to left."""
    seen = {ident: ()}
    for i, s in enumerate(gens):
        seen.setdefault(s, (i,))
    for i, s in enumerate(gens):
        for j, t in enumerate(gens):
            seen.setdefault(mul(s, t), (i, j))
    return list(seen.items())


def solve_lp(pictures, k):
    """Maximize t s.t. sum lam(a,b)(p[a]-p[b]) >= t on every picture p (tuple of 0/1 of length k)."""
    pairs = [(a, b) for a in range(k) for b in range(k) if a != b]
    P = np.array(pictures, dtype=float)
    A = np.stack([P[:, a] - P[:, b] for a, b in pairs], axis=1)  # rows: pictures
    nv = len(pairs) + 1
    c = np.zeros(nv)
    c[-1] = -1.0
    A_ub = np.hstack([-A, np.ones((A.shape[0], 1))])
    b_ub = np.zeros(A.shape[0])
    A_eq = np.zeros((1, nv))
    A_eq[0, :-1] = 1.0
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1.0],
                  bounds=[(0, None)] * len(pairs) + [(None, None)], method='highs')
    lam = np.maximum(res.x[:-1], 0)
    return pairs, lam, -res.fun


def exact_value(pairs, lam, pictures, denom=720):
    q = [Q(float(v)).limit_denominator(denom) for v in lam]
    tot = sum(q)
    q = [v / tot for v in q]
    val = min(sum(w * (p[a] - p[b]) for w, (a, b) in zip(q, pairs) if w) for p in pictures)
    support = {f'{a}-{b}': str(w) for w, (a, b) in zip(q, pairs) if w}
    return val, support


def free_case():
    win = window_words(W_GENS, W_ID, w_mul)
    elems = [g for g, _ in win]

    def in_E(w):  # reduced words whose first (leftmost) letter is b or b^-1
        return len(w) > 0 and abs(w[0]) == 2

    # For |x| >= 3 and |a| <= 2 the first letter of a x is fixed by a and the length-3 prefix of x,
    # so the rows for |x| <= 3 are all the rows that occur anywhere in F_2.
    xs = list(ball(W_GENS, W_ID, w_mul, 3))
    pics = sorted({tuple(int(in_E(w_mul(a, x))) for a in elems) for x in xs})
    pairs, lam, lpval = solve_lp(pics, len(elems))
    val, support = exact_value(pairs, lam, pics)
    return {'group': 'F_2', 'window': 'B_2', 'E': 'reduced words with first letter b^{+-1}',
            'window_elements': [list(w) for w in elems], 'distinct_pictures': len(pics),
            'lp_value': lpval, 'exact_value': str(val), 'exact_value_gt_half': val > Q(1, 2),
            'lambda': support}


def thompson_case(N):
    dist = ball(F_GENS, F_ID, f_mul, N)
    inv_idx = [1, 0, 3, 2]
    left = [{} for _ in F_GENS]  # left[i][x] = s_i * x when it lies in B_N
    for i, s in enumerate(F_GENS):
        for x in dist:
            y = f_mul(s, x)
            if y in dist:
                left[i][x] = y
    win = window_words(F_GENS, F_ID, f_mul)
    words = [w for _, w in win]

    def act(word, x):
        for i in reversed(word):
            x = left[i].get(x)
            if x is None:
                return None
        return x

    # first letters of geodesics: s_i is a left first letter of g if |s_i^-1 g| = |g| - 1
    first = {}
    for g, d in dist.items():
        first[g] = frozenset(i for i in range(4) if d > 0 and dist.get(left[inv_idx[i]].get(g), -9) == d - 1)
    out = []
    candidates = {
        'some geodesic starts with x1^{+-1}': lambda g: bool(first[g] & {2, 3}),
        'every geodesic starts with x1^{+-1}': lambda g: bool(first[g]) and first[g] <= {2, 3},
        'some geodesic starts with x0^{+-1}': lambda g: bool(first[g] & {0, 1}),
        'every geodesic starts with x0^{+-1}': lambda g: bool(first[g]) and first[g] <= {0, 1},
    }
    for n in range(4, N + 1):
        In = []
        for x, d in dist.items():
            if d > n:
                continue
            imgs = [act(w, x) for w in words]
            if all(y is not None and dist[y] <= n for y in imgs):
                In.append(imgs)
        for name, mem in candidates.items():
            pics = sorted({tuple(int(mem(y)) for y in imgs) for imgs in In})
            pairs, lam, lpval = solve_lp(pics, len(words))
            val, support = exact_value(pairs, lam, pics)
            out.append({'n': n, 'E': name, '|I_n|': len(In), 'distinct_pictures': len(pics),
                        'lp_value': lpval, 'exact_value': str(val),
                        'exact_value_gt_half': val > Q(1, 2)})
            print(json.dumps(out[-1]), file=sys.stderr, flush=True)
    return {'group': 'F', 'window': 'B_2', 'radii': [4, N], 'results': out}


if __name__ == '__main__':
    if sys.argv[1] == 'free':
        print(json.dumps(free_case(), indent=1))
    else:
        print(json.dumps(thompson_case(int(sys.argv[2])), indent=1))
