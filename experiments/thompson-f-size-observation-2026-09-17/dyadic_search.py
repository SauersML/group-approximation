"""Two-scale shadow laws for the tree-size observation.

Only roots 0..m are ever split by words of S_(m+1,m+d+1): after j-1 splits inside
roots 0..m those roots occupy positions 0..m+j-1, and i_j <= m+j-1.  So the
size pattern of split_s(Y) is the list of the m+d+1 pieces from roots 0..m,
followed by the tail t_(m+1), t_(m+2), ... shifted by exactly d.

Labels of top leaves:
  ('T', j)  complete binary tree of depth k+j (k large, uniform in [1, K]);
            split gives ('T', j-1), ('T', j-1); size 2^k * 2^j.
  ('INF', 'L'/'R')  comb of length uniform on [L, 2L], L >> 2^(k+J); split gives
            (INF, leaf) or (leaf, INF).
  'ONE'     a single leaf, size 1, cannot be split.
A piece that contains an INF has size 'inf'; otherwise it is either 1 or
2^k * c with c a positive dyadic rational.  If every s in S gives the same
pattern up to one global factor 2^(c_s), then the shadow law "k uniform, comb
lengths uniform" has total variation O(max|c_s| / K + 2^(K+J) / L) between
the size laws of split_s(Y) for all s, with the tail read exactly.
"""
import itertools
import sys
from fractions import Fraction


def split_node(x):
    if x == "ONE":
        return None
    if x[0] == "T":
        c = ("T", x[1] - 1)
        return (c, c)
    if x[0] == "INF":
        return (x, "ONE") if x[1] == "L" else ("ONE", x)
    return x  # caret (l, r)


def is_caret(x):
    return isinstance(x, tuple) and len(x) == 2 and not (x[0] in ("T", "INF"))


def size(x):
    if x == "ONE":
        return 1
    if x[0] == "T":
        return ("S", Fraction(2) ** x[1])
    if x[0] == "INF":
        return "inf"
    a, b = size(x[0]), size(x[1])
    if "inf" in (a, b):
        return "inf"
    if a == 1 and b == 1:
        return 2
    if isinstance(a, int) or isinstance(b, int):
        # mixing unscaled leaves with a scaled piece: scaled part dominates only
        # up to a bounded offset that powers of two do not absorb; forbid it.
        return "bad"
    if "bad" in (a, b):
        return "bad"
    return ("S", a[1] + b[1])


def fsize(x):
    s = size(x)
    return s


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


def pieces(config, word):
    cur = list(config)
    for i in word:
        s = split_node(cur[i])
        if s is None:
            return None
        cur = cur[:i] + list(s) + cur[i + 1:]
    return cur


def canon(pat):
    """Pattern up to one global power of two on the scaled entries."""
    sc = [p[1] for p in pat if isinstance(p, tuple)]
    if not sc:
        return tuple(pat)
    e = 0
    v = sc[0]
    while v >= 2:
        v /= 2
        e += 1
    while v < 1:
        v *= 2
        e -= 1
    f = Fraction(2) ** e
    return tuple(("S", p[1] / f) if isinstance(p, tuple) else p for p in pat)


def pattern(config, word):
    pc = pieces(config, word)
    if pc is None:
        return None
    pat = [fsize(x) for x in pc]
    if "bad" in pat:
        return None
    return canon(pat)


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


def tops(maxc, J):
    labels = [("T", j) for j in range(J + 1)] + [("INF", "L"), ("INF", "R"), "ONE"]
    out = []
    for n in range(maxc + 1):
        for t in shapes(n):
            out.extend(fill(t, labels))
    return out


def search(m, d, maxc, J, limit=5):
    S = monomial_set(m, d)
    T = tops(maxc, J)
    hits = []
    for config in itertools.product(T, repeat=m + 1):
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
    return S, T, hits


if __name__ == "__main__":
    maxc = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    J = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    cases = [(1, 1), (1, 2), (1, 3), (2, 2)]
    if len(sys.argv) > 3:
        cases = [tuple(int(x) for x in c.split(",")) for c in sys.argv[3:]]
    for (m, d) in cases:
        S, T, hits = search(m, d, maxc, J)
        print(f"m={m} d={d} |S|={len(S)} tops={len(T)} (<= {maxc} carets, J={J}): "
              f"{len(hits)} hits (first {len(hits)} shown)", flush=True)
        for c, p in hits:
            print("   config:", c)
            print("   pattern:", p, flush=True)
