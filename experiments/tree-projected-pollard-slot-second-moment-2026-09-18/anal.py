#!/usr/bin/env python3
"""Spectral test of the exact pair transfer printed by pairx.

Loads counts; for a given p builds the monotone map Phi on states
(letter, h) with |h| <= HS plus one far state per letter, and returns
  rho_up  = spectral radius of Phi / (9 w^2)      (upper bound: far rows by LP)
  rho_low = spectral radius of the truncated near operator / (9 w^2) (lower bound)
PASS (second moment bounded) iff rho_up < 1;  the ensemble FAILS for this
decoration if rho_low > 1 (then E Z_N^2/(E Z_N)^2 -> infinity).
"""
import sys
from collections import defaultdict
import numpy as np


def load(fn):
    ctx = {}
    cur = None
    for line in open(fn):
        a = line.split()
        if a[0] == 'ctx':
            cur = (int(a[1]), int(a[2]))
            ctx[cur] = dict(H=int(a[6]), DW=int(a[8]), KM=int(a[10]),
                            g=defaultdict(dict), n=defaultdict(lambda: defaultdict(dict)))
        elif a[0] == 'g':
            ctx[cur]['g'][int(a[1])][int(a[2])] = int(a[3])
        elif a[0] == 'n':
            ctx[cur]['n'][int(a[1])][int(a[2])][int(a[3])] = int(a[4])
    return ctx


def build(ctx, p, HS=None):
    if HS is None:
        HS = max(C['H'] for C in ctx.values())
    hs = list(range(-HS, HS + 1))
    nh = len(hs)
    L = 4
    nst = L * (nh + 1)
    M = np.zeros((nst, nst))          # near/near and near->far exact
    farrows = {}                      # letter ti -> list over t of (gmax(h') array, capN, Mtot)
    ws = set()
    for (ti, t), C in ctx.items():
        gval = {D: sum(v * p ** k for k, v in d.items()) for D, d in C['g'].items()}
        Mtot = sum(gval.values())
        for i, h in enumerate(hs):
            row = ti * (nh + 1) + i
            if abs(h) <= C['H']:
                masses = {hp: sum(v * p ** k for k, v in d.items()) for hp, d in C['n'][h].items()}
            else:
                masses = {h + D: v for D, v in gval.items()}
            for hp, v in masses.items():
                if abs(hp) <= HS:
                    M[row, t * (nh + 1) + hp + HS] += v
                else:
                    M[row, t * (nh + 1) + nh] += v
        # far row: sup over |h| > HS of exact translate rows
        gmax = np.zeros(nh)
        capN = 0.0
        for h in list(range(-HS - C['DW'] - 1, -HS)) + list(range(HS + 1, HS + C['DW'] + 2)):
            tot = 0.0
            for i, hp in enumerate(hs):
                v = gval.get(hp - h, 0.0)
                gmax[i] = max(gmax[i], v)
                tot += v
            capN = max(capN, tot)
        farrows.setdefault(ti, []).append((t, gmax, capN, Mtot))
        ws.add(round(Mtot, 12))
    return M, farrows, nh, hs


def phi(M, farrows, nh, y):
    z = M @ y
    for ti, lst in farrows.items():
        tot = 0.0
        for (t, gmax, capN, Mtot) in lst:
            yy = y[t * (nh + 1): t * (nh + 1) + nh]
            yF = y[t * (nh + 1) + nh]
            order = np.argsort(-yy)
            rem, capn, val = Mtot, capN, 0.0
            farused = False
            for i in order:
                if yy[i] <= yF and not farused:
                    val += rem * yF
                    rem = 0.0
                    farused = True
                    break
                a = min(gmax[i], capn, rem)
                val += a * yy[i]
                capn -= a
                rem -= a
                if rem <= 0:
                    break
            if not farused and rem > 0:
                val += rem * yF
            tot += val
        z[ti * (nh + 1) + nh] = tot
    return z


def rho(ctx, p, it=400):
    M, farrows, nh, hs = build(ctx, p)
    w = np.sqrt(max(r[3] for lst in farrows.values() for r in lst))
    Lnorm = 9 * w * w
    y = np.ones(M.shape[0])
    for _ in range(it):
        z = phi(M, farrows, nh, y)
        y = z / z.max()
    z = phi(M, farrows, nh, y)
    up = max(z[i] / y[i] for i in range(len(y)) if y[i] > 0) / Lnorm
    # truncated lower bound: near states only, no far
    idx = [ti * (nh + 1) + i for ti in range(4) for i in range(nh)]
    Mn = M[np.ix_(idx, idx)]
    low = max(abs(np.linalg.eigvals(Mn))) / Lnorm
    return up, low, w


if __name__ == '__main__':
    ctx = load(sys.argv[1])
    for ps in sys.argv[2:]:
        p = float(eval(ps))
        up, low, w = rho(ctx, p)
        print('p %.6f  3w %.5f  rho_up %.5f  rho_low %.5f' % (p, 3 * w, up, low))
