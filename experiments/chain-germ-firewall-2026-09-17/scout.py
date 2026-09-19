"""Kernel scout for the germ map theta : G_1 -> <sigma, delta, s> (germs at +inf).

Evaluates exact supports (via fast.py of the w16 lane) of words that are
nontrivial in G_1 but die in natural 'soluble' models, on one bulk period
[delta^n(5), delta^n(5) + 2^n) at delta-scale n.  Words are strings of letters:
S/s = sigma^{+-1}, R/r = rho^{+-1} with rho = s^-1 delta s, U/u = tau^{+-1}
with tau = s^-1 sigma s.  A word is applied right-to-left (last letter first).
usage: python3 scout.py {nonaffine|affine} n [word_name ...]
"""
import os
import sys
import time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'non-affine-doubling-lift-2026-09-17'))
from fast import *  # noqa: E402,F401,F403


def letters(ch):
    s, si, d, di = ch.s, ch.s_inv, ch.delta, ch.delta_inv
    L = {'S': T(ONE), 's': T(-ONE)}
    L['R'] = word(si, d, s)          # rho = s^-1 delta s
    L['r'] = word(si, di, s)
    L['U'] = word(si, T(ONE), s)     # tau = s^-1 sigma s
    L['u'] = word(si, T(-ONE), s)
    return L


def inv(w):
    return ''.join(c.swapcase() for c in reversed(w))


def comm(a, b):
    return a + b + inv(a) + inv(b)


WORDS = {
    # second derived subgroup of <rho, sigma>: dies when rho and sigma are
    # both affine, i.e. in the smooth model s' = x^2 of u-coordinates
    'rho_meta': comm(comm('R', 'S'), comm('R', 'SS')),
    # second derived subgroup of <tau, sigma>
    'tau_meta': comm(comm('U', 'S'), comm('U', 'SS')),
    'c1': comm('U', 'S'),
    'rho_c': comm('R', 'S'),
}


def bulk(ch, n):
    Pn = fx(5)
    for _ in range(n):
        Pn = ch.delta(Pn)[0]
    return Pn, Pn + (ONE << n)


def run(kind, n, names):
    ch = nonaffine() if kind == 'nonaffine' else affine_control()
    L = letters(ch)
    Pn, Qn = bulk(ch, n)
    for nm in names:
        w = WORDS[nm]
        h = word(*[L[c] for c in w])
        t = time.time()
        ivs, npc = support(h, Pn, Qn)
        m = sum(b - a for a, b in ivs)
        print(f"{kind} n={n} {nm:9s} len={len(w):3d} period [{f(Pn)},{f(Qn)})"
              f" pieces {npc} comps {len(ivs)} moved {f(m):.6g} ({time.time()-t:.0f}s)")
        sys.stdout.flush()


if __name__ == '__main__':
    run(sys.argv[1], int(sys.argv[2]), sys.argv[3:] or list(WORDS))
