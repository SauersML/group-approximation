#!/usr/bin/env python3
"""Single-row surfaces: b = rotation of Z/n, c = sigma a circle interval exchange with few pieces.
Computes rho_hat = max_{s,t <= S} rank([b^s,c^t]-I)/(s+t) with numpy and
d1 = min_a #{x : sigma(x) != x + a} (the exact cost with b fixed).
Usage: onerow.py n lengths...   (reverses the given interval lengths, i.e. the (l1,...,lk) -> (lk,...,l1) IET)"""
import sys
import numpy as np

def iet(lengths, twist=0):
    n = sum(lengths); starts = np.cumsum([0] + lengths[:-1])
    new = {}; pos = 0
    for i in reversed(range(len(lengths))):
        new[i] = pos; pos += lengths[i]
    sig = np.zeros(n, dtype=np.int64)
    for i, (st, l) in enumerate(zip(starts, lengths)):
        sig[st:st + l] = (np.arange(new[i], new[i] + l) + twist) % n
    return sig

def rank_minus_I(P):
    n = len(P); seen = np.zeros(n, bool); cyc = 0
    for i in range(n):
        if not seen[i]:
            cyc += 1; j = i
            while not seen[j]: seen[j] = True; j = P[j]
    return n - cyc

def profile(sig, S):
    n = len(sig); x = np.arange(n); best = (0, None)
    inv = np.argsort(sig)
    ct = x.copy(); cti = x.copy()
    for t in range(1, S + 1):
        ct = sig[ct]; cti = cti[inv]           # c^t and c^-t
        for s in range(1, S + 1):
            bs = (x + s) % n; bsi = (x - s) % n
            P = bs[ct[bsi[cti]]]                 # b^s c^t b^-s c^-t
            r = rank_minus_I(P) / (s + t)
            if r > best[0]: best = (r, (s, t))
    return best

def d1(sig):
    n = len(sig); a = (sig - np.arange(n)) % n
    return n - np.bincount(a, minlength=n).max()

if __name__ == "__main__":
    L = [int(v) for v in sys.argv[1:]] or [1, 2, 3]
    for lam in (1, 2, 4, 8, 16):
        sig = iet([lam * l for l in L]); n = len(sig)
        r, st = profile(sig, min(3 * n, 150))
        print(f"lengths {[lam*l for l in L]} n={n}: rho_hat={r:.3f} at (s,t)={st}, d1={d1(sig)}")
