#!/usr/bin/env python3
"""Lump the exact per-decoration transfer into the offset classes -c, 0, c, G
(sup over h in each class, and over the letter context), as the heights-uniform
LP map of engine.py does, and report rho(Phi_lumped)/(3 w^2).
This measures how much of the uniform method's loss is the class lumping itself
(as opposed to the counting bound)."""
import sys
import anal
import engine_p as engine
from fractions import Fraction as F


def lumped_T(ctx, p, c):
    cls = lambda h: {-c: 0, 0: 1, c: 2}.get(h, 3)
    T = [[0.0] * 5 for _ in range(4)]
    w2 = None
    for (ti, t), C in ctx.items():
        gval = {D: sum(v * p ** k for k, v in d.items()) for D, d in C['g'].items()}
        w2 = sum(gval.values())
        rows = {}
        for h in range(-C['H'] - C['DW'] - 2, C['H'] + C['DW'] + 3):
            if abs(h) <= C['H']:
                masses = {hp: sum(v * p ** k for k, v in d.items()) for hp, d in C['n'][h].items()}
            else:
                masses = {h + D: v for D, v in gval.items()}
            r = [0.0] * 5
            for hp, v in masses.items():
                r[cls(hp)] += v
                if hp != 0:
                    r[4] += v
            s = cls(h)
            for j in range(5):
                T[s][j] = max(T[s][j], r[j])
    return T, w2


if __name__ == '__main__':
    fn, c = sys.argv[1], int(sys.argv[2])
    ctx = anal.load(fn)
    for ps in sys.argv[3:]:
        p = float(eval(ps))
        T, w2 = lumped_T(ctx, p, c)
        L = 3 * w2
        Tn = [[a / L for a in r] for r in T]
        lam, y = engine.rho_phi(Tn, 1, 300)
        up, low, w = anal.rho(ctx, p, 200)
        print('p %.6f  lumped %.5f  exact %.5f' % (p, lam, up))
        for r in Tn:
            print('   ', [round(a, 5) for a in r])
