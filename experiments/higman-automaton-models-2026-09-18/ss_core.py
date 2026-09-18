# Core routines: self-similar actions of F(a,b,c,d) on the binary tree given by wreath recursions
#   g = (w_{g,0}, w_{g,1}) pi_g,   g(x v) = (x xor pi_g) . w_{g,x}(v),
# where the sections w_{g,x} are words in a,b,c,d and their inverses.
# Words are tuples of (gen, eps) with gen in 0..3 (a,b,c,d) and eps = +-1.
# A word acts as the composition l_1 o l_2 o ... o l_k (left action).
import numpy as np
from itertools import product

GENS = 4
LETTERS = [(g, e) for g in range(GENS) for e in (1, -1)]


def reduced_words(maxlen):
    out = [()]
    frontier = [()]
    for _ in range(maxlen):
        nf = []
        for w in frontier:
            for l in LETTERS:
                if w and w[-1][0] == l[0] and w[-1][1] == -l[1]:
                    continue
                nf.append(w + (l,))
        out += nf
        frontier = nf
    return out


def shift(w, s=1):
    return tuple(((g + s) % GENS, e) for g, e in w)


def word_perm(P, Pi, w, size):
    res = np.arange(size)
    for g, e in reversed(w):
        res = (P[g] if e == 1 else Pi[g])[res]
    return res


def power(p, k):
    res = np.arange(len(p))
    for _ in range(k):
        res = p[res]
    return res


def inv(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


def next_level(P, Pi, pis, secs, L):
    """P, Pi: level L-1 perms of the 4 generators. Returns level-L perms."""
    size = 1 << (L - 1)
    rest = np.arange(size)
    newP = []
    for g in range(GENS):
        arr = np.empty(2 * size, dtype=np.int64)
        for x in (0, 1):
            wp = word_perm(P, Pi, secs[g][x], size)
            arr[x + 2 * rest] = (x ^ pis[g]) + 2 * wp
        newP.append(arr)
    return newP, [inv(p) for p in newP]


def order(p):
    # order of a permutation = lcm of cycle lengths
    n = len(p)
    seen = np.zeros(n, dtype=bool)
    from math import lcm
    o = 1
    for i in range(n):
        if not seen[i]:
            j = i
            c = 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                c += 1
            o = lcm(o, c)
    return o


def check_rel(P, Pi, rel, size):
    lhs, rhs = rel
    return np.array_equal(word_perm(P, Pi, lhs, size), word_perm(P, Pi, rhs, size))


def higman_rels(n):
    # b^a = b^n : a^-1 b a = b^n, cyclically
    rels = []
    for g in range(GENS):
        x, y = (g + 1) % GENS, g  # y^-1 x y = x^n
        rels.append((((y, -1), (x, 1), (y, 1)), tuple([(x, 1)] * n)))
    return rels


def run(pis, secs, rels, Lmax):
    """Return the last level (<= Lmax) at which all rels hold, and final perms."""
    P = [np.zeros(1, dtype=np.int64) for _ in range(GENS)]
    Pi = [p.copy() for p in P]
    for L in range(1, Lmax + 1):
        P, Pi = next_level(P, Pi, pis, secs, L)
        size = 1 << L
        for r in rels:
            if not check_rel(P, Pi, r, size):
                return L - 1, P, Pi
    return Lmax, P, Pi
