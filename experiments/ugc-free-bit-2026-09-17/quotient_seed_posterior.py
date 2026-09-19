#!/usr/bin/env python3
"""Quotient seed posterior of the DKKMS 2-to-1 edge process.

Part 1 (exact).  For tiny (k, l=2) enumerate the per-tuple edge process
    V ~ smoothing(beta), R uniform line of X_V, L = R + <x> uniform with
    L meet H_U = 0,
map to the quotient Y = X_U / H_U (block F_2^3/<111> = F_2^2), and compare the
exact class posterior w(Rbar | Lbar) with the product formula
    w(Q | Lbar)  ~  prod_i [ (1-beta) + (beta/3) 2^(l-1) n_i(Q) ],
    n_i(Q) = #{v : f_{i,v} vanishes on the block-i image of Q}.

Part 2 (Monte Carlo, block product law).  Rows m_{i,v} in F_2^l as in the
node's proof; report E max_Q w(Q|Lbar) and E w(Q_0|Lbar) (Q_0 = generating
seed) at heavy smoothing beta = 0.5 and at beta = log log k / k.
Seed 20260917.  Exit 0 iff Part 1 errors are within the stated tolerance and
Part 2 shows concentration at beta = 0.5 (E w(Q_0) > 0.99 at the largest k).
"""
import math
import random
import sys
from collections import defaultdict

SEED = 20260917


def qmap_block(b):
    # F_2^3 / <111>  ->  F_2^2 :  (b0,b1,b2) -> (b0^b2, b1^b2)
    b0, b1, b2 = b & 1, (b >> 1) & 1, (b >> 2) & 1
    return (b0 ^ b2) | ((b1 ^ b2) << 1)


def qmap(vec, k):
    out = 0
    for i in range(k):
        out |= qmap_block((vec >> (3 * i)) & 7) << (2 * i)
    return out


# f_{i,v}: functional on F_2^2 with kernel <ebar_v>; ebar_0=(1,0), ebar_1=(0,1),
# ebar_2=(1,1).  f_0(y)=y1, f_1(y)=y0, f_2(y)=y0^y1.
def fvals(y2):
    y0, y1 = y2 & 1, (y2 >> 1) & 1
    return (y1, y0, y0 ^ y1)


def smoothings(k, beta):
    """Yield (prob, mask of X_V) over all smoothings V."""
    choices = [(1 - beta, 7)] + [(beta / 3, 1 << v) for v in range(3)]

    def rec(i, p, mask):
        if i == k:
            yield p, mask
            return
        for q, m in choices:
            yield from rec(i + 1, p * q, mask | (m << (3 * i)))
    yield from rec(0, 1.0, 0)


def in_HU(vec, k):
    return all(((vec >> (3 * i)) & 7) in (0, 7) for i in range(k))


def exact_part(k, beta, l=2):
    assert l == 2
    n = 3 * k
    P0 = defaultdict(float)
    for p, mask in smoothings(k, beta):
        d = bin(mask).count("1")
        sub = mask
        while sub:                      # nonzero r inside X_V
            P0[sub] += p / (2 ** d - 1)
            sub = (sub - 1) & mask
    joint = defaultdict(lambda: defaultdict(float))
    for r, pr in P0.items():
        if in_HU(r, k):
            continue
        wr = pr / (2 ** n - 2)
        rq = qmap(r, k)
        for x in range(1, 2 ** n):
            if x == r or in_HU(x, k) or in_HU(x ^ r, k):
                continue
            key = frozenset((rq, qmap(x, k), qmap(x ^ r, k)))
            joint[key][rq] += wr
    tot = sum(sum(d.values()) for d in joint.values())
    err_w, emax = 0.0, 0.0
    for key, d in joint.items():
        mass = sum(d.values())
        pred = {}
        for q in key:
            F = 1.0
            for i in range(k):
                ni = sum(1 for f in fvals((q >> (2 * i)) & 3) if f == 0)
                F *= (1 - beta) + (beta / 3) * 2 ** (l - 1) * ni
            pred[q] = F
        Z = sum(pred.values())
        for q in key:
            err_w += mass / tot * abs(d.get(q, 0.0) / mass - pred[q] / Z)
        emax += max(d.values()) / tot
    return err_w, emax


def part1():
    ok = True
    print("Part 1: exact quotient posterior vs product formula (l = 2)")
    print(" k  beta   E_C sum_Q |w - w_formula|   2^(l-k)   E_C max_Q w")
    for k in (2, 3):
        for beta in (0.05, 0.5, 0.9):
            e, m = exact_part(k, beta)
            print(f" {k}  {beta:4.2f}   {e:.3e}                  {2**(2-k):.3f}     {m:.4f}")
            ok &= e <= 3 * 2 ** (2 - k)
    return ok


def part2(samples=200):
    import numpy as np
    rng = np.random.default_rng(SEED)
    F2 = np.array([[0, 0], [1, 0], [0, 1], [1, 1]])       # Y_i elements
    # f_v(y) for v = 0,1,2 on the 4 elements of Y_i
    FV = np.array([[y[1], y[0], y[0] ^ y[1]] for y in F2])  # shape (4,3)
    ebar = [1, 2, 3]                                        # index of ebar_v
    print("\nPart 2: block product law, E max_Q w and E w(Q_0)  (Q_0 = generating seed)")
    print("  l  beta-rule        k     beta     E max_Q w   E w(Q_0)   1/(2^l-1)")
    last = {}
    for l in (3, 4):
        psis = np.arange(1, 2 ** l)
        psi0 = 1 << (l - 1)
        for rule in ("heavy 0.5", "loglogk/k"):
            for k in (50, 200, 800, 3200):
                beta = 0.5 if rule.startswith("heavy") else math.log(math.log(k)) / k
                logF = np.log((1 - beta) + (beta / 3) * 2 ** (l - 1) * np.arange(4))
                wm, w0 = 0.0, 0.0
                for _ in range(samples):
                    sm = rng.random(k) < beta
                    var = rng.integers(0, 3, k)
                    # generator images in Y_i (indices into F2): l-1 seed gens + x
                    g = rng.integers(0, 4, (k, l))
                    coin = rng.integers(0, 2, (k, l - 1))
                    eb = np.array(ebar)[var]
                    g[:, : l - 1] = np.where(sm[:, None], coin * eb[:, None], g[:, : l - 1])
                    # rows m_{i,v} as bitmasks over the l basis vectors
                    vals = FV[g]                                   # (k,l,3)
                    m = (vals * (1 << np.arange(l))[None, :, None]).sum(axis=1)  # (k,3)
                    lw = np.array([logF[((m == 0) | (m == p)).sum(axis=1)].sum() for p in psis])
                    w = np.exp(lw - lw.max()); w /= w.sum()
                    wm += w.max(); w0 += w[psi0 - 1]
                wm /= samples; w0 /= samples
                last[(l, rule)] = w0
                print(f"  {l}  {rule:12s} {k:6d}   {beta:.4f}    {wm:.4f}     {w0:.4f}     {1/(2**l-1):.4f}")
    return all(last[(l, "heavy 0.5")] > 0.99 for l in (3, 4))


if __name__ == "__main__":
    random.seed(SEED)
    ok1 = part1()
    ok2 = part2()
    print("\npart1 ok:", ok1, " part2 ok:", ok2)
    sys.exit(0 if (ok1 and ok2) else 1)
