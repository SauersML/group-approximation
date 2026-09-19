"""Generators as H_4 words (letters +-1..4 = s_1..s_4), copied from gens.py of
experiments/h4-two-flat-pencil-matching-2026-09-17 (positive-lift meridians w s_j^2 w^-1)."""
import itertools
from fmem import inv

FG = {'p3': [1, 1], 'p2': [1, 2, 2, -1], 'p1': [1, 2, 3, 3, -2, -1]}
NG = {'x0': [4, 4], 'x1': [3, 4, 4, -3], 'x3': [4, 3, 3, -4], 'x2': [3, 4, 3, 3, -4, -3],
      'x4': [2, 3, 4, 4, -3, -2], 'x11': [2, 4, 3, 3, -4, -2], 'x5': [2, 3, 4, 3, 3, -4, -3, -2],
      'x10': [3, 2, 4, 3, 3, -4, -2, -3], 'x6': [2, 3, 2, 4, 3, 3, -4, -2, -3, -2],
      'x9': [4, 3, 2, 4, 3, 3, -4, -2, -3, -4], 'x7': [2, 4, 3, 2, 4, 3, 3, -4, -2, -3, -4, -2],
      'x8': [3, 2, 4, 3, 2, 4, 3, 3, -4, -2, -3, -4, -2, -3]}
ZG = {'z2': [2, 2], 'z3': [3, 3], 'z23': [2, 3, 3, -2]}


def words(gens, L):
    """freely reduced words of length 1..L: list of (spec string, H_4 word)"""
    names = sorted(gens)
    let = [(n, 1) for n in names] + [(n, -1) for n in names]
    out = []
    for n in range(1, L + 1):
        for w in itertools.product(let, repeat=n):
            if any(w[k][0] == w[k + 1][0] and w[k][1] == -w[k + 1][1] for k in range(n - 1)):
                continue
            h = []
            for g, s in w:
                h += gens[g] if s == 1 else inv(gens[g])
            out.append((' '.join(g + ("'" if s < 0 else '') for g, s in w), h))
    return out


def word_of(spec, gens):
    h = []
    for t in spec.split():
        g = gens[t.rstrip("'")]
        h += inv(g) if t.endswith("'") else g
    return h
