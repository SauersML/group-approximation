"""Mixed-level padding: stable levels and independent levels.

Leaf labels of a top:
  'O'            an actual leaf (size 1);
  ('S', l, w)    atom of a *stable* level l with weight w: size lam_l * w^(1/a) * Z,
                 Z i.i.d. positive a-stable (0 < a < 1), lam_l log-uniform over a
                 long range, one lam_l shared by the whole level;
  ('I', l)       atom of an *independent* level l: size log-uniform on
                 [Lam_l, Lam_l^2], independently for every atom.
Levels are totally ordered, and sizes of higher levels dominate all lower sizes
by a large factor.  A piece's level is the max level of its atoms.  Its size is,
up to lower-level garbage,
  stable level:       lam_l * W^(1/a) * Z'   with W = sum of its top-level weights
                      (a-stable additivity);
  independent level:  its single top-level atom (two or more: inadmissible);
  level 0:            its exact leaf count.
If for every s in S the pieces of roots 0..m have the same levels, the same
level-0 sizes, and, for each stable level, weight vectors proportional to one
vector, then the size laws of split_s(Y) agree up to a total variation that
tends to 0 as the ranges grow: log-uniform lam_l absorbs the proportionality
factor, and flat densities absorb lower-level garbage and rounding.
"""
import itertools
import sys
from fractions import Fraction
from functools import lru_cache

from level_search import monomial_set, shapes, fill, root_words


def labels_for(types, weights):
    labs = ['O']
    for l, ty in enumerate(types, start=1):
        if ty == 'S':
            labs += [('S', l, w) for w in weights]
        else:
            labs.append(('I', l))
    return labs


def tops(maxc, labs):
    out = []
    for n in range(1, maxc + 1):
        for t in shapes(n):
            out.extend(fill(t, labs))
    return out


def is_leaf(x):
    return x == 'O' or (isinstance(x, tuple) and len(x) > 0 and x[0] in ('S', 'I'))


@lru_cache(maxsize=None)
def summ(x):
    """(level, kind, stat, zeros): stat = weight sum (S) or atom count (I)."""
    if x == 'O':
        return (0, '0', 0, 1)
    if is_leaf(x):
        if x[0] == 'S':
            return (x[1], 'S', x[2], 0)
        return (x[1], 'I', 1, 0)
    a, b = summ(x[0]), summ(x[1])
    z = a[3] + b[3]
    if a[0] > b[0]:
        return (a[0], a[1], a[2], z)
    if b[0] > a[0]:
        return (b[0], b[1], b[2], z)
    return (a[0], a[1], a[2] + b[2], z)


def raw(pc):
    out = []
    for x in pc:
        lev, kind, stat, z = summ(x)
        if lev == 0:
            out.append(('0', z))
        elif kind == 'I':
            if stat != 1:
                return None
            out.append(('I', lev))
        else:
            out.append(('S', lev, Fraction(stat)))
    return out


def canon(lab):
    first = {}
    res = []
    for p in lab:
        if p[0] == 'S':
            if p[1] not in first:
                first[p[1]] = p[2]
            res.append(('S', p[1], p[2] / first[p[1]]))
        else:
            res.append(p)
    return tuple(res)


def split_all(config, word):
    cur = list(config)
    for i in word:
        x = cur[i]
        if is_leaf(x):
            return None
        cur = cur[:i] + [x[0], x[1]] + cur[i + 1:]
    return cur


def pattern(config, word, lo=None, hi=None):
    pc = split_all(config, word)
    if pc is None:
        return None
    if lo is not None:
        pc = pc[lo:hi]
    r = raw(pc)
    if r is None:
        return None
    return canon(r)


def search(m, d, maxc, types, weights, limit=3):
    S = monomial_set(m, d)
    labs = labels_for(types, weights)
    T = tops(maxc, labs)
    cands = []
    for a in range(m + 1):
        S_a = root_words(S, a)
        good = []
        for t in T:
            cfg = ['O'] * a + [t] + ['O'] * (m - a)
            first = None
            ok = True
            for w in S_a:
                p = pattern(cfg, w, a, a + d + 1)
                if p is None or (first is not None and p != first):
                    ok = False
                    break
                first = p
            if ok:
                good.append(t)
        cands.append(good)
    hits = []
    for config in itertools.product(*cands):
        first = None
        ok = True
        for w in S:
            p = pattern(config, w)
            if p is None or (first is not None and p != first):
                ok = False
                break
            first = p
        if ok:
            hits.append((config, first))
            if len(hits) >= limit:
                break
    return S, [len(c) for c in cands], hits


if __name__ == "__main__":
    maxc = int(sys.argv[1])
    types = sys.argv[2]
    weights = [int(x) for x in sys.argv[3].split(",")]
    cases = [tuple(int(x) for x in c.split(",")) for c in sys.argv[4:]]
    for (m, d) in cases:
        S, nc, hits = search(m, d, maxc, types, weights)
        print(f"m={m} d={d} |S|={len(S)} carets<={maxc} levels={types} weights={weights}: "
              f"per-root candidates {nc}; hits {len(hits)}", flush=True)
        for c, p in hits:
            print("   config:", c)
            print("   pattern:", p, flush=True)
