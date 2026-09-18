#!/usr/bin/env python3
"""Exact check of the distortion inputs used by
research/faithful-actions-with-subexponential-orbit-growth-exclude-sl3z.md.

1. SL_3(Z): with D = diag(1, A), A = [[2,1],[1,1]], x12 = I+E12, x13 = I+E13,
   x23 = I+E23, the word
       w_N = D^{-k_1} u_1 D^{k_1-k_2} u_2 ... D^{k_{m-1}-k_m} u_m D^{k_m}
   built from the Zeckendorf expansion N = sum F_{j_i} (u = x12, k = (j-1)/2 for
   odd j; u = x13, k = j/2 for even j) has first-row entry (0, N, *), and
   [w_N, x23] = x13^N.  Its length is at most 4*k_max + 2m + 2 = O(log N).
2. H_3(Z): c^{m^2} = [a^m, b^m] for a = x12, b = x23, c = x13, length 4m.

Every matrix identity is verified with exact integer arithmetic.
Run: python3 sl3z_root_distortion_words.py
"""
import math
import random


def mul(X, Y):
    return tuple(tuple(sum(X[i][t] * Y[t][j] for t in range(3)) for j in range(3))
                 for i in range(3))


I3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def elem(i, j, v=1):
    M = [list(r) for r in I3]
    M[i][j] = v
    return tuple(tuple(r) for r in M)


D = ((1, 0, 0), (0, 2, 1), (0, 1, 1))
Dinv = ((1, 0, 0), (0, 1, -1), (0, -1, 2))
x12, x13, x23 = elem(0, 1), elem(0, 2), elem(1, 2)
x23inv = elem(1, 2, -1)
assert mul(D, Dinv) == I3


def fibs(limit):
    F = [0, 1]
    while F[-1] <= limit:
        F.append(F[-1] + F[-2])
    return F


def zeckendorf(N, F):
    js = []
    j = len(F) - 1
    while N > 0:
        while F[j] > N:
            j -= 1
        js.append(j)
        N -= F[j]
        j -= 2
    return js  # indices j >= 2, pairwise non-consecutive


def word_for(N):
    """Return the word for x13^N as a list of (letter, exponent) syllables."""
    F = fibs(N)
    terms = []
    for j in zeckendorf(N, F):
        if j % 2 == 1:
            terms.append(((j - 1) // 2, "x12"))
        else:
            terms.append((j // 2, "x13"))
    terms.sort()
    ks = [k for k, _ in terms]
    assert len(set(ks)) == len(ks), "two terms share a conjugation depth"
    w = []
    prev = 0
    for k, u in terms:
        w.append(("D", prev - k))
        w.append((u, 1))
        prev = k
    w.append(("D", prev))
    # commutator [w, x23] = w x23 w^-1 x23^-1
    winv = [(u, -e) for u, e in reversed(w)]
    return w + [("x23", 1)] + winv + [("x23", -1)]


def evaluate(word):
    gens = {"D": (D, Dinv), "x12": (x12, elem(0, 1, -1)),
            "x13": (x13, elem(0, 2, -1)), "x23": (x23, x23inv)}
    M = I3
    for u, e in word:
        g = gens[u][0] if e > 0 else gens[u][1]
        for _ in range(abs(e)):
            M = mul(M, g)
    return M


def length(word):
    return sum(abs(e) for _, e in word)


def fast_eval(word):
    """Same product, with D-powers computed by repeated squaring (for huge N)."""
    def mpow(X, Xinv, e):
        B = X if e > 0 else Xinv
        e = abs(e)
        R = I3
        while e:
            if e & 1:
                R = mul(R, B)
            B = mul(B, B)
            e >>= 1
        return R
    gens = {"D": (D, Dinv), "x12": (x12, elem(0, 1, -1)),
            "x13": (x13, elem(0, 2, -1)), "x23": (x23, x23inv)}
    M = I3
    for u, e in word:
        M = mul(M, mpow(*gens[u], e))
    return M


def main():
    worst = 0.0
    for N in range(1, 20001):
        w = word_for(N)
        assert evaluate(w) == elem(0, 2, N), N
        if N >= 2:
            worst = max(worst, length(w) / math.log(N))
    print("SL3(Z): x13^N verified for 1 <= N <= 20000; max |w_N| / ln N =",
          round(worst, 3))
    rng = random.Random(20260917)
    for digits in (30, 60, 120):
        N = rng.randrange(10 ** (digits - 1), 10 ** digits)
        w = word_for(N)
        assert fast_eval(w) == elem(0, 2, N)
        print(f"  N with {digits} digits: |w_N| = {length(w)}, ln N = {math.log(N):.1f}")
    for m in range(1, 40):
        a_m, b_m = elem(0, 1, m), elem(1, 2, m)
        comm = mul(mul(mul(a_m, b_m), elem(0, 1, -m)), elem(1, 2, -m))
        assert comm == elem(0, 2, m * m)
    print("H3(Z): c^(m^2) = [a^m, b^m] verified for 1 <= m < 40 (length 4m)")


if __name__ == "__main__":
    main()
