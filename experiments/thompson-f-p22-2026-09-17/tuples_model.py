#!/usr/bin/env python3
"""Five-root tuple model of the P_(2,2) doubling problem for Thompson's F.

Positive monoid M of F: normal forms x_(i_1)...x_(i_D), i_1 <= ... <= i_D, relations
x_j x_i = x_i x_(j+1) (i < j).  Forest model: an element is an infinite sequence of binary trees
(t_0, t_1, ...), all but finitely many trivial; the word x_(a_1)...x_(a_k) is built by applying
carets in the order a_k, ..., a_1, each joining the current roots a, a+1.  So s*y is the forest of y
with the carets of s added on top of its roots.  The letter of a caret in the normal form is the
number of leaves strictly left of its leftmost leaf.

Reduction.  Every s in S_(3,5) (= X_2 X_3, nine normal forms) touches only roots 0..4 of y, and the
nine maps T^5 -> T^3 are the nine ways to add two carets reducing five roots to three.  So for
Y subset M split by the tail (t_5, t_6, ...) the ratio |S Y|/|Y| is at least the minimum over
tails, and the doubling problem for S_(3,5) is exactly the problem for finite A subset T^5.

This script (1) checks the forest model against normal-form multiplication on random data,
(2) computes lambda5(n) = min |S A|/|A| over A subset T^5 with n carets by min cut + Dinkelbach
for small n, and compares min_(n<=D) lambda5(n) with the exact Lambda_(S_(3,5))(D) recorded in
thompson-f-monomial-doubling-ratio-is-a-finite-computation.
"""
import itertools, random, sys
from fractions import Fraction
from functools import lru_cache

LEAF = 0


@lru_cache(maxsize=None)
def trees(c):
    if c == 0:
        return (LEAF,)
    out = []
    for i in range(c):
        for u in trees(i):
            for v in trees(c - 1 - i):
                out.append((u, v))
    return tuple(out)


def carets(t):
    return 0 if t == LEAF else 1 + carets(t[0]) + carets(t[1])


def leaves(t):
    return 1 if t == LEAF else leaves(t[0]) + leaves(t[1])


def normal_form(forest):
    """forest: list of trees (roots 0..k-1, trivial afterwards)."""
    letters = []
    off = 0

    def walk(t, off):
        if t == LEAF:
            return 1
        letters.append(off)
        l = walk(t[0], off)
        r = walk(t[1], off + l)
        return l + r

    for t in forest:
        off += walk(t, off)
    return tuple(sorted(letters))


def left_mul_letter(j, w):
    out = []
    k = 0
    while k < len(w) and w[k] < j:
        out.append(w[k]); j += 1; k += 1
    out.append(j)
    out.extend(w[k:])
    return tuple(out)


def mul(a, b):
    r = tuple(b)
    for letter in reversed(a):
        r = left_mul_letter(letter, r)
    return r


S35 = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3)]


def merge(forest, i):
    f = list(forest)
    return f[:i] + [(f[i], f[i + 1])] + f[i + 2:]


def apply_word(word, forest):
    f = list(forest)
    for letter in reversed(word):
        f = merge(f, letter)
    return f


def split_maps():
    """The nine maps T^5 -> T^3, as functions on 5-tuples."""
    return [lambda a, s=s: tuple(apply_word(s, list(a))) for s in S35]


def check_model(trials=4000, seed=1):
    rng = random.Random(seed)
    for _ in range(trials):
        k = rng.randint(5, 8)
        forest = [rng.choice(trees(rng.randint(0, 3))) for _ in range(k)]
        w = normal_form(forest)
        for s in S35:
            if normal_form(apply_word(s, forest)) != mul(s, w):
                raise SystemExit("model mismatch")
    # injectivity of normal form on 5-tuples with <= 4 carets
    seen = {}
    for n in range(5):
        for comp in itertools.product(range(n + 1), repeat=5):
            if sum(comp) != n:
                continue
            for tup in itertools.product(*[trees(c) for c in comp]):
                nf = normal_form(list(tup))
                if nf in seen and seen[nf] != tup:
                    raise SystemExit("normal form not injective")
                seen[nf] = tup
    return True


def tuples5(n):
    out = []
    for comp in itertools.product(range(n + 1), repeat=5):
        if sum(comp) != n:
            continue
        out.extend(itertools.product(*[trees(c) for c in comp]))
    return out


def lambda5(n):
    import numpy as np
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import maximum_flow
    U = tuples5(n)
    maps = split_maps()
    img_id = {}
    edges = []
    for ai, a in enumerate(U):
        for f in maps:
            g = f(a)
            gid = img_id.setdefault(g, len(img_id))
            edges.append((ai, gid))
    nu, ng = len(U), len(img_id)
    src, snk = nu + ng, nu + ng + 1
    ratio = Fraction(ng, nu)
    while True:
        K, J = ratio.numerator, ratio.denominator
        rows, cols, caps = [], [], []
        for ai in range(nu):
            rows.append(src); cols.append(ai); caps.append(K)
        INF = K * nu + 1
        for ai, gid in set(edges):
            rows.append(ai); cols.append(nu + gid); caps.append(INF)
        for gid in range(ng):
            rows.append(nu + gid); cols.append(snk); caps.append(J)
        m = csr_matrix((np.array(caps, dtype=np.int32), (rows, cols)), shape=(nu + ng + 2,) * 2)
        res = maximum_flow(m, src, snk)
        best = K * nu - res.flow_value
        if best <= 0:
            return ratio
        # recover the source side
        flow = res.flow.tocsr()
        resid = (m - flow)
        import collections
        seen = [False] * (nu + ng + 2)
        dq = collections.deque([src]); seen[src] = True
        rev = flow.T.tocsr()
        while dq:
            v = dq.popleft()
            row = resid.getrow(v)
            for w, c in zip(row.indices, row.data):
                if c > 0 and not seen[w]:
                    seen[w] = True; dq.append(w)
            row = rev.getrow(v)
            for w, c in zip(row.indices, row.data):
                if c > 0 and not seen[w]:
                    seen[w] = True; dq.append(w)
        Y = [ai for ai in range(nu) if seen[ai]]
        SY = {gid for ai, gid in edges if seen[ai]}
        ratio = Fraction(len(SY), len(Y))


LAMBDA = [Fraction(28, 5), Fraction(9, 2), Fraction(277, 70), Fraction(835, 231), Fraction(2816, 835),
          Fraction(4178, 1307)]

if __name__ == "__main__":
    check_model()
    print("forest model agrees with normal-form multiplication; normal form injective on T^5 (n<=4)")
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    best = None
    for n in range(0, nmax + 1):
        l5 = lambda5(n)
        best = l5 if best is None else min(best, l5)
        ref = LAMBDA[n - 1] if 1 <= n <= len(LAMBDA) else None
        print(f"n={n} |T^5_n|={len(tuples5(n))} lambda5={l5} ~{float(l5):.6f} min_(<=n)={best}"
              + (f" Lambda(D={n})={ref} match={best == ref}" if ref is not None else ""))
