"""Right-germ evaluation: every map returns (value, slope, extent) such that the
map is affine with that slope on [x, x + extent).  Composition keeps this
exact, so walking x -> x + extent enumerates the affine pieces of any word
exactly (Fractions throughout).  Used to find the exact support of c1 and of
w_k on windows at large scales."""
from fractions import Fraction as Fr
from math import floor

INF = None


def _mn(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return a if a < b else b


class RPL:
    """Increasing PL map on [xs[0], xs[-1]) (right germs)."""

    def __init__(self, xs, ys):
        self.xs = [Fr(v) for v in xs]
        self.ys = [Fr(v) for v in ys]

    def g(self, x):
        xs, ys = self.xs, self.ys
        assert xs[0] <= x < xs[-1], (float(x), float(xs[0]), float(xs[-1]))
        for i in range(len(xs) - 1):
            if x < xs[i + 1]:
                m = (ys[i + 1] - ys[i]) / (xs[i + 1] - xs[i])
                return ys[i] + m * (x - xs[i]), m, xs[i + 1] - x
        raise AssertionError

    def inv(self):
        return RPL(self.ys, self.xs)


def comp(fg, gg):
    """germ of f o g from germ functions."""
    def h(x):
        y, mg, rg = gg(x)
        z, mf, rf = fg(y)
        return z, mf * mg, _mn(rg, None if rf is None else rf / mg)
    return h


class ChainG:
    def __init__(self, d_xs, d_ys, X, s0_xs, s0_ys):
        self.d = RPL(d_xs, d_ys)
        self.dinv = self.d.inv()
        self.d0 = self.d.ys[0]
        self.X = Fr(X)
        self.s0 = RPL(s0_xs, s0_ys)
        self.s0inv = self.s0.inv()
        self.Y = self.s0.ys[0]
        self.dX = self.delta(self.X)[0]
        self.ddY = self.delta(self.delta(self.Y)[0])[0]
        assert self.s0.xs[-1] == self.dX and self.s0.ys[-1] == self.ddY

    def delta(self, x):
        n = floor(x)
        y, m, r = self.d.g(x - n)
        return 2 * n + y, m, r

    def delta_inv(self, y):
        n = floor((y - self.d0) / 2)
        x, m, r = self.dinv.g(y - 2 * n)
        return n + x, m, r

    def s(self, x):
        # s = delta^(2n) s0 delta^-n
        n, m, r = 0, Fr(1), None
        while x >= self.dX:
            x, m1, r1 = self.delta_inv(x)
            r = _mn(r, r1 / m)
            m = m * m1
            n += 1
        y, m1, r1 = self.s0.g(x)
        r = _mn(r, r1 / m)
        m = m * m1
        for _ in range(2 * n):
            y, m1, r1 = self.delta(y)
            r = _mn(r, r1 / m)
            m = m * m1
        return y, m, r

    def s_inv(self, y):
        n, m, r = 0, Fr(1), None
        while y >= self.ddY:
            for _ in range(2):
                y, m1, r1 = self.delta_inv(y)
                r = _mn(r, r1 / m)
                m = m * m1
            n += 1
        x, m1, r1 = self.s0inv.g(y)
        r = _mn(r, r1 / m)
        m = m * m1
        for _ in range(n):
            x, m1, r1 = self.delta(x)
            r = _mn(r, r1 / m)
            m = m * m1
        return x, m, r


def T(c):
    return lambda x: (x + c, Fr(1), None)


def word(*fs):
    """germ of fs[0] o fs[1] o ... o fs[-1]."""
    h = fs[-1]
    for f in reversed(fs[:-1]):
        h = comp(f, h)
    return h


def pieces(h, a, b):
    """exact list of affine pieces (start, slope, value) of h on [a, b)."""
    out = []
    x = Fr(a)
    while x < b:
        y, m, r = h(x)
        out.append((x, m, y))
        assert r is not None and r > 0
        x = x + r
    return out


def support(h, a, b):
    """exact support (union of maximal intervals where h != id) inside [a,b)."""
    ivs = []
    cur = None
    x = Fr(a)
    npieces = 0
    while x < b:
        y, m, r = h(x)
        npieces += 1
        ident = (m == 1 and y == x)
        end = min(x + r, Fr(b))
        if not ident:
            if cur is not None and cur[1] == x:
                cur[1] = end
            else:
                cur = [x, end]
                ivs.append(cur)
        x = x + r
    return ivs, npieces


def nonaffine():
    d_xs = [0, Fr(1, 2), Fr(3, 4), 1]
    d_ys = [Fr(1, 2), 1, Fr(3, 2), Fr(5, 2)]
    return ChainG(d_xs, d_ys, 4, [4, 8, Fr(33, 4), Fr(17, 2)], [16, 48, 49, 65])


def affine_control():
    return ChainG([0, 1], [0, 2], 4, [4, 6, 8], [16, 32, 64])


def elements(ch):
    s, si = ch.s, ch.s_inv
    tau = word(si, T(1), s)
    taui = word(si, T(-1), s)
    c1 = word(tau, T(1), taui, T(-1))
    c1i = word(T(1), tau, T(-1), taui)
    return dict(tau=tau, taui=taui, c1=c1, c1i=c1i)


def wk(ch, k):
    e = elements(ch)
    ck = word(T(k), e['c1'], T(-k))
    cki = word(T(k), e['c1i'], T(-k))
    return word(e['c1'], ck, e['c1i'], cki)
