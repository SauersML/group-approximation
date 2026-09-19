"""Numerical sanity check for chain-group-germ-models-are-generically-faithful.

Model on the whole line: sigma = x+1, delta = 2x, s = psi o (x|x|) o psi^-1,
where psi commutes with 2x.  On each side psi(x) = +-2^Psi(log2|x|) with
Psi(t) = t + p(t), p 1-periodic, Psi an increasing PL map with random nodes.
psi = id is the smooth model (rho = sqrt2 x, and [rho sigma rho^-1, sigma] = 1).

Letters (applied right to left): S/s sigma^+-1, D/d delta^+-1, A/a s^+-1,
R/r rho^+-1 with rho = s^-1 delta s, U/u tau^+-1 with tau = s^-1 sigma s.
Prints max |w(x) - x| over a grid of x in [3, 40] for each test word.
usage: python3 check.py [seed ...]      (seed 'id' means psi = id)
"""
import bisect
import math
import random
import sys
from mpmath import mp, mpf, log, power

mp.dps = 60


def make_Psi(rng, k=6):
    """Increasing PL map Psi of R with Psi(t+1) = Psi(t)+1, random nodes."""
    xs = sorted(rng.random() for _ in range(k))
    ys = sorted(rng.random() for _ in range(k))
    xs = [mpf(x) for x in xs]
    ys = [mpf(y) for y in ys]
    X = [xs[-1] - 1] + xs + [xs[0] + 1]
    Y = [ys[-1] - 1] + ys + [ys[0] + 1]
    return X, Y


def pl_eval(X, Y, t):
    n = mp.floor(t)
    f = t - n
    # shift f into [X[0], X[0]+1)
    while f < X[0]:
        f += 1; n -= 1
    while f >= X[0] + 1:
        f -= 1; n += 1
    i = bisect.bisect_right(X, f) - 1
    i = min(i, len(X) - 2)
    y = Y[i] + (Y[i + 1] - Y[i]) * (f - X[i]) / (X[i + 1] - X[i])
    return y + n


class Model:
    def __init__(self, seed):
        if seed == 'id':
            self.P = None
        else:
            rng = random.Random(seed)
            self.P = {1: make_Psi(rng), -1: make_Psi(rng)}

    def psi(self, x, inv=False):
        if x == 0 or self.P is None:
            return x
        sg = 1 if x > 0 else -1
        X, Y = self.P[sg]
        if inv:
            X, Y = Y, X
        return sg * power(2, pl_eval(X, Y, log(abs(x), 2)))

    def s(self, x, inv=False):
        y = self.psi(x, inv=True)
        y = y * abs(y) if not inv else (mp.sqrt(y) if y >= 0 else -mp.sqrt(-y))
        return self.psi(y)

    def letter(self, c, x):
        if c == 'S': return x + 1
        if c == 's': return x - 1
        if c == 'D': return 2 * x
        if c == 'd': return x / 2
        if c == 'A': return self.s(x)
        if c == 'a': return self.s(x, inv=True)
        raise ValueError(c)


EXPAND = {'R': 'aDA', 'r': 'adA', 'U': 'aSA', 'u': 'asA'}


def inv(w):
    return ''.join(c.swapcase() for c in reversed(w))


def comm(a, b):
    return a + b + inv(a) + inv(b)


def expand(w):
    return ''.join(EXPAND.get(c, c) for c in w)


c1 = comm('U', 'S')
WORDS = {
    'rc=[R S r, S]': comm('RSr', 'S'),
    'c1=[U,S]': c1,
    'w3=[c1,S^3 c1 S^-3]': comm(c1, 'SSS' + c1 + 'sss'),
    'rho_meta': comm(comm('R', 'S'), comm('R', 'SS')),
    'tau_meta': comm(comm('U', 'S'), comm('U', 'SS')),
}


def apply(m, w, x):
    for c in reversed(expand(w)):
        x = m.letter(c, x)
    return x


def run(seed):
    m = Model(seed)
    grid = [mpf(3) + mpf(37) * i / 400 for i in range(401)]
    for nm, w in WORDS.items():
        d = max(abs(apply(m, w, x) - x) for x in grid)
        print(f"psi={seed:>4} {nm:22s} len={len(expand(w)):3d} max|w(x)-x| = {float(d):.3e}")


if __name__ == '__main__':
    for sd in (sys.argv[1:] or ['id', '1', '2', '3']):
        run(sd if sd == 'id' else int(sd))
