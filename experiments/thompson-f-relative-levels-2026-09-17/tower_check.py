"""Mechanical checks of the structural facts used by the tower law.

Node: research/thompson-f-tower-size-laws-have-zero-defect.md (and its -proof companion).

The tower law puts complete depth-d tops on roots 0..m and a tree X_v with n_v carets and depth
e_v at the depth-d leaf v = 0..N-1 (global left-to-right order, N = (m+1) 2^d); the tail is
trivial.  The proof uses three combinatorial facts, checked here for several (m, d):

  (a) for every word s of S_(m+1,m+d+1), the pieces p_0..p_(m+d) of split_s z hang from nodes
      x_j at depth h_j <= d, and the leaf sets below x_0, ..., x_(m+d) are consecutive intervals
      I_0 < I_1 < ... < I_(m+d) that partition 0..N-1;
  (b) |p_j| = (2^(d-h_j) - 1) + sum_(v in I_j) n_v  and  dep p_j = (d - h_j) + max_(v in I_j) e_v,
      computed on explicit forests with split_word (random small (n_v, e_v));
  (c) a tree with n carets and depth e exists iff ceil(log2(n+1)) <= e <= n (n >= 1), and
      make_tree(n, e) builds one; checked for all n <= 60.

Usage: python3 tower_check.py
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "thompson-f-shadow-defect-2026-09-17"))
from exact_tail_shadow_defect import LEAF, caret, carets, depth, split_word, monomial_set  # noqa: E402

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "thompson-f-size-observation-2026-09-17"))
from equal_middle_lp import antichain  # noqa: E402


def balanced(r):
    """Tree with r carets and minimal depth ceil(log2(r+1))."""
    if r == 0:
        return LEAF
    a = (r - 1) // 2
    return caret(balanced(a), balanced(r - 1 - a))


def make_tree(n, e):
    """Tree with n carets and depth e; requires ceil(log2(n+1)) <= e <= n, or n = e = 0."""
    if n == 0:
        assert e == 0
        return LEAF
    assert e >= 1 and e <= n <= 2 ** e - 1, (n, e)
    r = min(n - e, 2 ** (e - 1) - 1)
    return caret(make_tree(n - 1 - r, e - 1), balanced(r))


def all_leaves(m, d):
    return [(a, format(k, "0%db" % d)) for a in range(m + 1) for k in range(2 ** d)]


def complete_top(d, fill):
    """Complete depth-d tree whose leaves (left to right) carry the trees in `fill`."""
    if d == 0:
        return fill.pop(0)
    left = complete_top(d - 1, fill)
    right = complete_top(d - 1, fill)
    return caret(left, right)


def check_intervals(m, d):
    LV = all_leaves(m, d)
    S = monomial_set(m, d)
    out = []
    for s in S:
        nodes = antichain(m, s)
        assert len(nodes) == m + d + 1
        ivs = []
        for a, q in nodes:
            I = [i for i, (b, r) in enumerate(LV) if b == a and r.startswith(q)]
            assert len(q) <= d and I == list(range(I[0], I[-1] + 1)) and len(I) == 2 ** (d - len(q))
            ivs.append((I[0], I[-1], len(q)))
        assert ivs[0][0] == 0 and ivs[-1][1] == len(LV) - 1
        assert all(ivs[j][1] + 1 == ivs[j + 1][0] for j in range(len(ivs) - 1))
        out.append((s, ivs))
    return out


def check_formulas(m, d, trials, rng):
    words = check_intervals(m, d)
    N = (m + 1) * 2 ** d
    bad = 0
    for _ in range(trials):
        ne = []
        for _ in range(N):
            n = rng.randint(1, 12)
            lo = (n + 1 - 1).bit_length()  # ceil(log2(n+1))
            ne.append((n, rng.randint(lo, n)))
        X = [make_tree(n, e) for n, e in ne]
        forest = tuple(complete_top(d, X[a * 2 ** d:(a + 1) * 2 ** d]) for a in range(m + 1))
        for s, ivs in words:
            y = split_word(forest, s)
            if y is None or len(y) != m + d + 1:
                bad += 1
                continue
            for j, (lo, hi, h) in enumerate(ivs):
                size = 2 ** (d - h) - 1 + sum(ne[v][0] for v in range(lo, hi + 1))
                dep = d - h + max(ne[v][1] for v in range(lo, hi + 1))
                if carets(y[j]) != size or depth(y[j]) != dep:
                    bad += 1
    return len(words), bad


def check_realizability(nmax=60):
    bad = 0
    for n in range(1, nmax + 1):
        lo = n.bit_length()  # ceil(log2(n+1))
        assert 2 ** (lo - 1) - 1 < n <= 2 ** lo - 1
        for e in range(lo, n + 1):
            t = make_tree(n, e)
            if carets(t) != n or depth(t) != e:
                bad += 1
    return bad


if __name__ == "__main__":
    rng = random.Random(20260919)
    print("(c) realizability: failures for n <= 60:", check_realizability())
    for m, d in [(0, 1), (0, 2), (1, 1), (0, 3), (1, 2), (2, 1), (0, 4), (1, 3), (2, 2), (3, 1),
                 (1, 4), (2, 3), (0, 5)]:
        nw, bad = check_formulas(m, d, trials=20, rng=rng)
        print(f"(m,d)=({m},{d}) width={m + d}: words={nw}  (a) consecutive intervals OK  "
              f"(b) size/depth formula failures over 20 random forests = {bad}")
