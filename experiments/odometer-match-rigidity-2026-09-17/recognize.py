#!/usr/bin/env python3
"""Calibration for fpbs-odometer-killing-code-is-two-sided-injective.

Builds the symmetric odometer code of fpbs-quasiconvex-null-small-classes-exist-on-free-boundary on Z/2^K
with the extra admissible choices of the proof:
  (A1) every Toeplitz fill uses the letter a (so the unperturbed sign sequence is the regular paperfolding
       sequence p(2^k u) = chi(u), chi(u) = +1 iff u = 1 mod 4);
  (A2) the stage-n_j window starts at r_j in {q/8+1, q/8+2} and has l_j + 1 < 2^(n_j - C), C = 5;
  (A3) delta = sum_j 2 l_j / q_{n_j} <= 2^-C.
Then it checks, on the finite model:
  1. the unperturbed paperfolding alternation densities (odd class 1, even class exactly 1/2);
  2. the overwrite relative densities eta_k in every class {y = 2^k mod 2^(k+1)} against delta + 2^-C;
  3. the recognition algorithm of Lemma 2 (parity test, then majority per class) recovers x mod 2^(K-1)
     from the forward sign itinerary s(x+1), s(x+2), ... and from the backward itinerary s(x), s(x-1), ...
     for every residue x (full period), and for random x from a window of length q/4 only.
"""
import random

K = 16
C = 5
q = 2 ** K
random.seed(7)


def chi(u):
    return 1 if u % 4 == 1 else -1


def p(y):
    y %= q
    if y == 0:
        return None
    while y % 2 == 0:
        y //= 2
    return chi(y)


# signs of the code: start from paperfolding, then overwrite windows at stages n_j (q_n = 2^(n+2))
stages = [(8, 6), (12, 100)]   # (n_j, l_j)
s = [p(y) for y in range(q)]
ov = [False] * q
delta = 0.0
for n, l in stages:
    qn = 2 ** (n + 2)
    assert l + 1 < 2 ** (n - C)
    delta += 2 * l / qn
    r = qn // 8 + random.choice((1, 2))
    word = [random.choice((1, -1)) for _ in range(l)]
    for base in range(0, q, qn):
        for i in range(l):
            y = (base + r + i) % q
            z = (base - r - i) % q
            s[y] = word[i]
            s[z] = -word[i]      # odd symmetry F(-y) = F(y)^-1 flips the sign
            ov[y] = ov[z] = True
assert delta <= 2 ** -C
print(f"K = {K}, q = {q}, stages (n_j, l_j) = {stages}, delta = {delta:.4f} <= 2^-C = {2**-C:.4f}")

# 1. paperfolding alternation densities
odd = [y for y in range(1, q, 2)]
even = [y for y in range(2, q - 2, 2)]
alt_odd = sum(p(y + 2) == -p(y) for y in odd if p(y + 2) is not None) / len(odd)
alt_even = sum(p(y + 2) == -p(y) for y in even) / len(even)
print(f"1. paperfolding: P(p(y+2) = -p(y) | y odd) = {alt_odd:.4f}, | y even) = {alt_even:.4f}")

# 2. overwrite relative densities
worst = 0.0
for k in range(K - 1):
    cls = range(2 ** k, q, 2 ** (k + 1))
    eta = sum(ov[y] for y in cls) / len(cls)
    worst = max(worst, eta)
    assert eta <= delta + 2 ** -C + 1e-12, (k, eta)
eta_even = sum(ov[y] for y in range(0, q, 2)) / (q // 2)
print(f"2. max_k eta_k = {worst:.4f} <= delta + 2^-C = {delta + 2**-C:.4f}; even-class density = {eta_even:.4f}")


def recognize(seq, forward=True):
    """seq[i] = s(x+i+1) (forward) or s(x-i) (backward), i = 0..N-1; returns x mod 2^(K-1).
    Only the signs are used; the offsets d(i) = i+1 or -i are known, x is not."""
    N = len(seq)
    d = (lambda i: i + 1) if forward else (lambda i: -i)
    # parity: the class of offsets whose signs alternate in steps of 2 is the odd class of y = x + d
    score = {}
    for c in (0, 1):
        idx = [i for i in range(N - 2) if d(i) % 2 == c]
        j = 2 if forward else 2      # y+2 sits at i+2 forward, y-2 at i+2 backward: both are sign flips on odd y
        ok = [seq[i + j] == -seq[i] for i in idx if seq[i] is not None and seq[i + j] is not None]
        score[c] = sum(ok) / max(1, len(ok))
    codd = max(score, key=score.get)          # x + codd is odd
    x = (1 - codd) % 2
    for k in range(0, K - 2):
        M = 2 ** (k + 1)
        # indices i with (x + d(i)) = 2^k mod M
        if forward:
            i0 = (2 ** k - x - 1) % M
        else:
            i0 = (x - 2 ** k) % M
        agree = tot = 0
        for i in range(i0, N, M):
            if seq[i] is None:
                continue
            u = ((x + d(i)) % (2 * M)) // 2 ** k
            agree += seq[i] == chi(u)
            tot += 1
        if agree < tot - agree:
            x += M
        x %= 2 * M
    return x, score


fails = 0
for x in range(0, q, 1021):
    fwd = [s[(x + t) % q] for t in range(1, q + 1)]
    bwd = [s[(x - t) % q] for t in range(q)]
    rf, _ = recognize(fwd, True)
    rb, _ = recognize(bwd, False)
    fails += (rf != x % 2 ** (K - 1)) + (rb != x % 2 ** (K - 1))
print(f"3a. full-period recognition, {len(range(0, q, 1021))} residues, forward and backward: {fails} failures")
fails = 0
for _ in range(60):
    x = random.randrange(q)
    fwd = [s[(x + t) % q] for t in range(1, q // 4 + 1)]
    rf, sc = recognize(fwd, True)
    # a window of length q/4 only sees classes k <= K-3 reliably: compare mod 2^(K-3)
    fails += (rf % 2 ** (K - 3)) != x % 2 ** (K - 3)
print(f"3b. window q/4, 60 random x, compare mod 2^(K-3): {fails} failures; sample parity scores {sc}")
