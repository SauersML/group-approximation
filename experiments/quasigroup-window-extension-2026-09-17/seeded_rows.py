"""Seeded search for Ledrappier sub-SFTs with large windows.

For a seed row x (a long prefix of a substitutive sequence over F_2) we compute the
rows F^n x, F = 1 + sigma (Ledrappier: x(i, t+1) = x(i, t) + x(i+1, t) mod 2), for
n < NT, and record which length-L words occur in some row, looking only at
positions that stay inside the prefix. If W_L misses a word for every L below some
bound, then A = W_L is a candidate window set: Omega(A) contains the orbit closure
of the seed (if the finite-prefix statistics are faithful).

Usage: python3 seeded_rows.py
"""
import numpy as np


def fixed_point(sub, start, length):
    w = [start]
    while len(w) < length:
        w = [c for a in w for c in sub[a]]
    return np.array(w[:length], dtype=np.uint8)


SEEDS = {
    "thue-morse": ({0: [0, 1], 1: [1, 0]}, 0),
    "period-doubling": ({0: [0, 1], 1: [0, 0]}, 0),
    "fibonacci": ({0: [0, 1], 1: [0]}, 0),
    "toeplitz3-aab": ({0: [0, 0, 1], 1: [0, 0, 0]}, 0),
    "toeplitz3-aba": ({0: [0, 1, 0], 1: [0, 0, 0]}, 0),
    "base3-010-101": ({0: [0, 1, 0], 1: [1, 0, 1]}, 0),
    "base3-001-110": ({0: [0, 0, 1], 1: [1, 1, 0]}, 0),
    "base5-00101-11010": ({0: [0, 0, 1, 0, 1], 1: [1, 1, 0, 1, 0]}, 0),
    "chacon": ({0: [0, 0, 1, 0], 1: [1]}, 0),
}


def word_sets(x, NT, Lmax):
    seen = {L: set() for L in range(1, Lmax + 1)}
    row = x.copy()
    for n in range(NT):
        m = len(row)
        for L in range(1, Lmax + 1):
            if m < L:
                continue
            # integer code of each length-L window
            codes = np.zeros(m - L + 1, dtype=np.int64)
            for s in range(L):
                codes = codes * 2 + row[s:m - L + 1 + s]
            seen[L].update(np.unique(codes).tolist())
        row = (row[:-1] ^ row[1:])
    return seen


if __name__ == "__main__":
    N, NT, Lmax = 1 << 15, 4096, 12
    for name, (sub, a) in SEEDS.items():
        x = fixed_point(sub, a, N)
        seen = word_sets(x, NT, Lmax)
        full = [L for L in range(1, Lmax + 1) if len(seen[L]) == 2 ** L]
        print(name, "missing counts:",
              {L: 2 ** L - len(seen[L]) for L in range(1, Lmax + 1)},
              "first full L:", full[:1])
