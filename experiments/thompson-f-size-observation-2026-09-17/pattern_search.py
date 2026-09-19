"""Search for comb-padded shadow laws that kill the tree-size observation.

Model.  Each of the first I+1 trees t_0..t_I is a finite *top* with exactly one
marked leaf INF, which stands for a comb of huge uniform length: INF_L is a left
comb (splitting it gives INF_L, leaf), INF_R a right comb (leaf, INF_R).  The tail
t_(I+1), ... is arbitrary and is shifted by exactly d by every split_s, s of
degree d, so it does not matter.  The size pattern of split_s(Y) is the list of
the I+d+1 antichain sizes, with 'inf' for the piece holding INF.  When every
s in S gives the same pattern, and the big pieces differ from the comb lengths
by bounded offsets, comb lengths uniform on [L, 2L] give total variation O(1/L)
between the size laws of split_s(Y), s in S.

Stage 1 searches deterministic configurations.  Stage 2 (optional) searches
mixtures by a linear program over configurations.
"""
import itertools
import sys

LEAF = ()


def inf(t):
    return ("INF", t)


def is_inf(x):
    return isinstance(x, tuple) and len(x) == 2 and x[0] == "INF"


def split_node(x):
    if x == LEAF:
        return None
    if is_inf(x):
        return (x, LEAF) if x[1] == "L" else (LEAF, x)
    return x


def size(x):
    if x == LEAF:
        return 1
    if is_inf(x):
        return "inf"
    a, b = size(x[0]), size(x[1])
    return "inf" if "inf" in (a, b) else a + b


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


def trees(n):
    """All plane binary trees with n carets."""
    if n == 0:
        return [LEAF]
    out = []
    for k in range(n):
        for l in trees(k):
            for r in trees(n - 1 - k):
                out.append((l, r))
    return out


def mark(t):
    """All ways to replace one leaf of t by INF_L or INF_R."""
    if t == LEAF:
        return [inf("L"), inf("R")]
    l, r = t
    return [(x, r) for x in mark(l)] + [(l, x) for x in mark(r)]


def tops(maxc):
    out = []
    for n in range(maxc + 1):
        for t in trees(n):
            out.extend(mark(t))
    return out


def pattern(config, word):
    cur = list(config)
    for i in word:
        if i >= len(cur):
            return None
        s = split_node(cur[i])
        if s is None:
            return None
        cur = cur[:i] + list(s) + cur[i + 1:]
    return tuple(size(x) for x in cur)


def stage1(m, d, maxc):
    S = monomial_set(m, d)
    I = m + d - 1
    T = tops(maxc)
    hits = []
    for config in itertools.product(T, repeat=I + 1):
        pats = set()
        for w in S:
            p = pattern(config, w)
            if p is None:
                break
            pats.add(p)
            if len(pats) > 1:
                break
        else:
            if len(pats) == 1:
                hits.append((config, pats.pop()))
    return S, hits


if __name__ == "__main__":
    maxc = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    for (m, d) in [(1, 1), (1, 2), (2, 2), (1, 3)]:
        S, hits = stage1(m, d, maxc)
        print(f"m={m} d={d} |S|={len(S)} tops<= {maxc} carets: {len(hits)} deterministic hits")
        for c, p in hits[:3]:
            print("   ", c, "->", p)
