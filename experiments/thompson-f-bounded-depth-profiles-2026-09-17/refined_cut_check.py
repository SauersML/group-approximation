#!/usr/bin/env python3
"""Structural check for `thompson-f-bounded-depth-subtree-profiles-have-zero-defect`.

Shadow law architecture: m+1 complete binary tops of depth d+r, with a tree X_v hung at
leaf v (v = 1..N, N = (m+1) 2^(d+r), numbered left to right), trivial tail.

For every word s of the Guba set S_(m+1,m+d+1) (normal forms, `monomial_set`) we check:
  (a) split_s Z is defined and never cuts below the tops (the placeholders are untouched);
  (b) split_s Z has exactly w+1 = m+d+1 non-trivial pieces;
  (c) every piece has a complete top of depth >= r;
  (d) the (m+d+1) 2^r depth-r descendants of the pieces, left to right, carry consecutive
      dyadic intervals of placeholders that partition 1..N  (the *refined cut*);
  (e) after substituting random explicit trees X_v, the subtree at each depth-r descendant
      has  carets = (2^k - 1) + sum_{v in I} |X_v|  and  depth = k + max_{v in I} dep X_v,
      where 2^k = |I|;  and the pieces agree with `split_word` of the repository helper
      `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py`.
Run: python3 refined_cut_check.py      (stdlib only, a few seconds)
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "thompson-f-shadow-defect-2026-09-17"))
import exact_tail_shadow_defect as H  # noqa: E402

LEAF = H.LEAF


def top(depth, ids):
    """Complete depth-`depth` top; its leaves are the integer placeholders `ids`."""
    if depth == 0:
        return ids[0]
    h = len(ids) // 2
    return (top(depth - 1, ids[:h]), top(depth - 1, ids[h:]))


def lsplit(forest, k):
    f = list(forest)
    t = f[k]
    assert isinstance(t, tuple) and len(t) == 2, "split would cut below the tops"
    return f[:k] + [t[0], t[1]] + f[k + 1:]


def descendants(t, r):
    """Nodes at depth r, left to right; None if the top-r of t is not complete."""
    if r == 0:
        return [t]
    if not (isinstance(t, tuple) and len(t) == 2):
        return None
    a, b = descendants(t[0], r - 1), descendants(t[1], r - 1)
    return None if a is None or b is None else a + b


def ids_below(t):
    return [t] if isinstance(t, int) else ids_below(t[0]) + ids_below(t[1])


def top_depth(t):
    return 0 if isinstance(t, int) else 1 + top_depth(t[0])


def substitute(t, X):
    return X[t] if isinstance(t, int) else (substitute(t[0], X), substitute(t[1], X))


def random_tree(rng, n):
    if n == 0:
        return LEAF
    k = rng.randrange(n)
    return (random_tree(rng, k), random_tree(rng, n - 1 - k))


def check(m, d, r, rng, trials=3):
    N = (m + 1) * 2 ** (d + r)
    Z = [top(d + r, list(range(a * 2 ** (d + r) + 1, (a + 1) * 2 ** (d + r) + 1)))
         for a in range(m + 1)]
    words = H.monomial_set(m, d)
    fails = 0
    for s in words:
        y = list(Z)
        for i in s:
            y = lsplit(y, i)                                   # (a)
        if len(y) != m + d + 1:                                # (b)
            fails += 1
            continue
        blocks = []
        for p in y:
            desc = descendants(p, r)                           # (c)
            if desc is None:
                fails += 1
                break
            for q in desc:
                blocks.append(ids_below(q))
        flat = [v for b in blocks for v in b]
        if len(blocks) != (m + d + 1) * 2 ** r or flat != list(range(1, N + 1)):
            fails += 1                                         # (d)
            continue
        if any(len(b) != 2 ** top_depth(q) for b, q in
               zip(blocks, [q for p in y for q in descendants(p, r)])):
            fails += 1
            continue
        for _ in range(trials):                                # (e)
            X = {v: random_tree(rng, rng.randrange(0, 6)) for v in range(1, N + 1)}
            real = H.split_word(H.trim(tuple(substitute(t, X) for t in Z)), s)
            mine = tuple(substitute(p, X) for p in y)
            if real is None or H.trim(mine) != real:
                fails += 1
                continue
            for p in y:
                for q in descendants(p, r):
                    I = ids_below(q)
                    k = top_depth(q)
                    sub = substitute(q, X)
                    if H.carets(sub) != 2 ** k - 1 + sum(H.carets(X[v]) for v in I):
                        fails += 1
                    if H.depth(sub) != k + max(H.depth(X[v]) for v in I):
                        fails += 1
    return len(words), fails


def main():
    rng = random.Random(20260917)
    total = 0
    print("m d r |S| intervals=(m+d+1)2^r N fails")
    for m, d, r in [(0, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 1), (2, 1, 2), (0, 3, 2),
                    (2, 2, 1), (1, 3, 1), (3, 1, 1), (2, 2, 2), (0, 4, 1), (1, 2, 3)]:
        n, f = check(m, d, r, rng)
        total += f
        print(m, d, r, n, (m + d + 1) * 2 ** r, (m + 1) * 2 ** (d + r), f)
    print("TOTAL FAILURES", total)
    return 0 if total == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
