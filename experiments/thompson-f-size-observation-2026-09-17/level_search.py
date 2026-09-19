"""Leveled comb padding: finite search for shadow laws of the size observation.

A *top* is a finite plane binary tree whose leaves carry levels 0, 1, 2, ...
  level 0   an actual leaf (size 1);
  level l>0 an *atom*: an unsplit subtree whose size is log-uniform on
            [Lam_l, Lam_l^2], independently of everything else, with
            Lam_1 << Lam_2 << ... (Lam_(l+1) >> Lam_l^2 times the number of atoms).
A node of the top has level = max level of its leaves.  A piece of split_s(Y)
is *admissible* when its level is 0, or it contains exactly one atom of its
level.  Its size is then (that atom) + (bounded lower-level garbage), or an
exact integer at level 0.

Pattern of s = for each of the m+d+1 pieces of roots 0..m: its level (>0), or
('0', exact size).  If all s in S give the same pattern with all pieces
admissible, the size laws of split_s(Y), s in S, are within total variation
O(sum_l (#atoms) Lam_(l-1)^2 / Lam_l) of each other (induction on levels: the
top-level atoms are i.i.d. with a density that is flat at the scale of the
garbage), jointly with any exact tail (the tail is shifted by d for every s).

Stage: per-root filter (words that split only root a must agree), then join.
"""
import itertools
import sys
from functools import lru_cache


def monomial_set(m, d):
    out = []

    def rec(prefix, j):
        if j == d:
            out.append(tuple(prefix))
            return
        lo = prefix[-1] if prefix else 0
        for i in range(lo, m + j + 1):
            rec(prefix + [i], j + 1)

    rec([], 0)
    return sorted(out)


def shapes(n):
    if n == 0:
        return ["*"]
    out = []
    for k in range(n):
        for l in shapes(k):
            for r in shapes(n - 1 - k):
                out.append((l, r))
    return out


def fill(t, labels):
    if t == "*":
        for lab in labels:
            yield lab
        return
    for l in fill(t[0], labels):
        for r in fill(t[1], labels):
            yield (l, r)


def tops(maxc, lmax):
    out = []
    for n in range(maxc + 1):
        for t in shapes(n):
            out.extend(fill(t, list(range(lmax + 1))))
    return out


@lru_cache(maxsize=None)
def summary(x):
    """(level, count of leaves at that level, number of level-0 leaves)."""
    if isinstance(x, int):
        return (x, 1, 1 if x == 0 else 0)
    a, b = summary(x[0]), summary(x[1])
    z = a[2] + b[2]
    if a[0] > b[0]:
        return (a[0], a[1], z)
    if b[0] > a[0]:
        return (b[0], b[1], z)
    return (a[0], a[1] + b[1], z)


def piece_label(x):
    lev, cnt, z = summary(x)
    if lev == 0:
        return ("0", z)
    if cnt != 1:
        return None
    return lev


def pieces(config, word):
    cur = list(config)
    for i in word:
        x = cur[i]
        if isinstance(x, int):
            return None
        cur = cur[:i] + [x[0], x[1]] + cur[i + 1:]
    return cur


def pattern(config, word):
    pc = pieces(config, word)
    if pc is None:
        return None
    lab = tuple(piece_label(x) for x in pc)
    if None in lab:
        return None
    return lab


def root_words(S, a):
    return [w for w in S if all(i == a for i in w[:1]) and
            all(a <= i <= a + j for j, i in enumerate(w))]


def root_ok(t, a, m, S_a):
    """Words that split only root a: root a's pieces must agree."""
    first = None
    for w in S_a:
        cfg = [0] * a + [t] + [0] * (m - a)
        pc = pieces(cfg, w)
        if pc is None:
            return False
        lab = tuple(piece_label(x) for x in pc[a:a + len(w) + 1])
        if None in lab:
            return False
        if first is None:
            first = lab
        elif lab != first:
            return False
    return True


def search(m, d, maxc, lmax, limit=3):
    S = monomial_set(m, d)
    T = tops(maxc, lmax)
    cands = []
    for a in range(m + 1):
        S_a = root_words(S, a)
        cands.append([t for t in T if not isinstance(t, int) and root_ok(t, a, m, S_a)])
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
    lmax = int(sys.argv[2])
    cases = [tuple(int(x) for x in c.split(",")) for c in sys.argv[3:]]
    for (m, d) in cases:
        S, nc, hits = search(m, d, maxc, lmax)
        print(f"m={m} d={d} |S|={len(S)} tops<={maxc} carets, levels<={lmax}: "
              f"per-root candidates {nc}; hits {len(hits)}", flush=True)
        for c, p in hits:
            print("   config:", c)
            print("   pattern:", p, flush=True)
