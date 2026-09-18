"""Truncated odometer flux D_K for words in R = <M_11, a, b, c> (and alpha, beta, gamma).

Digits: letter k -> digit k-2 (k = 2..11), letter 1 -> digit 10; digit 0 is least significant,
so a is x -> x + 1 on Z_11.  Right action (x w)^g = x^{pi_g} w^{g|_x}.

For a word w, t_w(x) = x^w - x is computed exactly modulo 11^N and lifted to (-11^N/2, 11^N/2].
Candidate singular points are the preimages of -1 = 10^omega under the prefixes of w before each
b- or c-letter.  D_K(w) = 11^-N * sum of t_w over x outside the level-K cylinders around them.
Claim checked: D_K(w) = e_a(w) + K e_c(w) + O(11^-K), and D_K(w) is independent of N.
"""
import random
from fractions import Fraction
import numpy as np

D = 11


def cyc_perm(cycles):
    p = list(range(D))
    for cyc in cycles:
        for i, x in enumerate(cyc):
            p[x] = cyc[(i + 1) % len(cyc)]
    return p


def letters_to_digits(cycles):
    f = lambda k: 10 if k == 1 else k - 2
    return [[f(k) for k in cyc] for cyc in cycles]


ID = list(range(D))
ALPHA = [(x + 1) % D for x in range(D)]
BETA = cyc_perm(letters_to_digits([(1, 2, 3, 4, 8), (5, 10, 7, 11, 6)]))
GAMMA = cyc_perm(letters_to_digits([(3, 7, 11, 8), (4, 10, 5, 6)]))  # ATLAS M11 generator

# state -> (root permutation on digits, {digit: section state})
AUT = {
    'a': (ALPHA, {10: 'a'}),
    'b': (ID, {10: 'b', 0: 'A', 1: 'B'}),
    'c': (ID, {10: 'c', 0: 'a'}),
    'A': (ALPHA, {}),
    'B': (BETA, {}),
    'G': (GAMMA, {}),
}
INV = {s: [p.index(y) for y in range(D)] for s, (p, _) in AUT.items()}


def act(s, inv, X, depth):
    if depth == 0 or X.size == 0:
        return X
    perm, sec = AUT[s]
    d, r = X % D, X // D
    if not inv:
        nd = np.array(perm)[d]
        for x, t in sec.items():
            m = d == x
            r[m] = act(t, False, r[m], depth - 1)
    else:
        nd = np.array(INV[s])[d]
        for x, t in sec.items():
            m = nd == x
            r[m] = act(t, True, r[m], depth - 1)
    return nd + D * r


def flux(word, N, K):
    M = D ** N
    X = np.arange(M, dtype=np.int64)
    T = X.copy()
    sing = []
    for (s, inv) in word:
        if s in 'bc':
            sing.append(int(np.nonzero(T == M - 1)[0][0]))
        T = act(s, inv, T, N)
    t = (T - X) % M
    t = np.where(t > M // 2, t - M, t)
    keep = np.ones(M, dtype=bool)
    for q in sing:
        keep &= (X % D ** K) != (q % D ** K)
    return Fraction(int(t[keep].sum()), M)


def exps(word):
    ea = sum((-1 if inv else 1) for s, inv in word if s == 'a')
    ec = sum((-1 if inv else 1) for s, inv in word if s == 'c')
    return ea, ec


if __name__ == '__main__':
    random.seed(20260917)
    gens = ['a', 'b', 'c', 'A', 'B', 'G']
    words = [[('a', False)], [('c', False)], [('b', False)], [('c', True)],
             [('a', False), ('c', False), ('a', True), ('c', True)]]
    for _ in range(40):
        L = random.randint(2, 7)
        words.append([(random.choice(gens), random.random() < 0.5) for _ in range(L)])
    worst = {}
    for w in words:
        ea, ec = exps(w)
        name = ''.join(s + ("'" if i else '') for s, i in w)
        row = []
        for (N, K) in [(5, 2), (6, 2), (6, 3), (6, 4)]:
            v = flux(w, N, K)
            err = v - (ea + K * ec)
            worst[(N, K)] = max(worst.get((N, K), 0), abs(err))
            row.append(f"N{N}K{K}:{float(v):+.5f}")
        print(f"{name:24s} e_a={ea:+d} e_c={ec:+d} " + ' '.join(row))
    for k, v in sorted(worst.items()):
        print(f"max |D_K - (e_a + K e_c)| at N={k[0]}, K={k[1]}: {float(v):.3e}"
              f"  (11^-K = {11.0 ** -k[1]:.3e})")
