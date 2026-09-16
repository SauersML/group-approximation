"""Sanity checks for research/artifacts/braid-centralizer-characters-2026-09-16.md.

(1) Lemma L (laminar independence): for every maximal laminar family F of
    subsets of [n] of size >= 2 (these are exactly the full binary
    hierarchies on [n]), the pair-indicator vectors chi_S (S in F) are
    linearly independent over Q.  Independence passes to subfamilies, so this
    covers all laminar families.  Also checks that the "private pair" of each
    S is contained in a member S' of F iff S' contains S.
(2) Linking numbers of twists (input B2): for random braids w and blocks
    S = {a..b}, the pure braid w * Delta_S^2 * w^-1 has lk_{ij} = 1 exactly
    when {i, j} is inside perm_w(S), and 0 otherwise.  lk_{ij} of a pure braid
    is half the signed count of crossings between strands i and j.
Single-threaded, deterministic seed, small output.
"""
import itertools, random
from fractions import Fraction

def hierarchies(items):
    """All maximal laminar families (as lists of frozensets, size >= 2) on items."""
    items = tuple(items)
    if len(items) == 1:
        yield []
        return
    first, rest = items[0], items[1:]
    # split items into two nonempty blocks, first element in block A
    for r in range(0, len(rest)):
        for comb in itertools.combinations(rest, r):
            A = (first,) + comb
            B = tuple(x for x in rest if x not in comb)
            if not B:
                continue
            for fa in hierarchies(A):
                for fb in hierarchies(B):
                    yield fa + fb + [frozenset(items)]

def rank(rows):
    M = [[Fraction(x) for x in row] for row in rows]
    rk, cols = 0, len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c] / M[rk][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def private_pair(S, F):
    children = [T for T in F if T < S and not any(T < U < S for U in F)]
    if len(children) >= 2:
        return (min(children[0]), min(children[1]))
    if len(children) == 1:
        return (min(children[0]), min(S - children[0]))
    a, b = sorted(S)[:2]
    return (a, b)

def check_laminar(nmax=7):
    for n in range(2, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        count = 0
        for F in hierarchies(range(n)):
            count += 1
            rows = [[1 if (i in S and j in S) else 0 for (i, j) in pairs] for S in F]
            assert rank(rows) == len(F), (n, F)
            for S in F:
                p = set(private_pair(S, F))
                for T in F:
                    assert (p <= T) == (S <= T), (n, F, S, T)
        print(f"n={n}: {count} maximal laminar families, all independent, private pairs ok")

def lk_vector(word, n):
    """word: list of (p, e), letter sigma_p^e (0-based p, strands at p, p+1).
    Returns (permutation, dict of signed crossing counts between strand labels)."""
    pos = list(range(n))  # pos[k] = label of strand currently at position k
    cross = {}
    for p, e in word:
        a, b = pos[p], pos[p + 1]
        key = (min(a, b), max(a, b))
        cross[key] = cross.get(key, 0) + e
        pos[p], pos[p + 1] = b, a
    return pos, cross

def delta_sq(a, b):
    """Full twist on positions a..b (inclusive): (sigma_a ... sigma_{b-1})^(b-a+1)."""
    k = b - a + 1
    return [(p, 1) for p in range(a, b)] * k

def inverse(word):
    return [(p, -e) for (p, e) in reversed(word)]

def check_lk(trials=400, seed=20260916):
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(3, 8)
        a = rng.randint(0, n - 2)
        b = rng.randint(a + 1, n - 1)
        w = [(rng.randint(0, n - 2), rng.choice((1, -1))) for _ in range(rng.randint(0, 25))]
        word = w + delta_sq(a, b) + inverse(w)
        pos, cross = lk_vector(word, n)
        assert pos == list(range(n)), "conjugate of pure braid must be pure"
        # label of the strand that w puts at position q (reading w first, bottom to top)
        posw, _ = lk_vector(w, n)
        S = {posw[q] for q in range(a, b + 1)}
        for i, j in itertools.combinations(range(n), 2):
            c = cross.get((i, j), 0)
            assert c % 2 == 0
            expected = 1 if (i in S and j in S) else 0
            assert c // 2 == expected, (n, a, b, w, i, j, c)
    print(f"lk check: {trials} random conjugated full twists, all lk_ij = [{{i,j}} in S]")

if __name__ == "__main__":
    check_laminar()
    check_lk()
