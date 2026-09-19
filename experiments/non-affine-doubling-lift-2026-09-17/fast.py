"""Fast exact right-germ evaluation with dyadic fixed point integers.

A number is an int v standing for v / 2^E.  Every map in play is dyadic PL
(slopes powers of 2, dyadic breakpoints), so values are dyadic; we assert
exactness of every division.  A germ is (value, slope exponent a, extent)
meaning: affine with slope 2^a on [x, x + extent).
"""
E = 400
ONE = 1 << E


def fx(num, den=1):
    v = num * ONE
    assert v % den == 0
    return v // den


def div2(v, a):
    """v / 2^a exactly."""
    if a >= 0:
        assert v % (1 << a) == 0, "precision"
        return v >> a
    return v << (-a)


def mul2(v, a):
    return div2(v, -a)


def ext_div(r, a):
    """conservative extent r / 2^a (floor)."""
    if r is None:
        return None
    if a >= 0:
        return r >> a
    return r << (-a)


def _mn(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return a if a < b else b


class RPL:
    def __init__(self, xs, ys):
        self.xs = list(xs)
        self.ys = list(ys)
        self.a = []
        for i in range(len(xs) - 1):
            dx, dy = xs[i + 1] - xs[i], ys[i + 1] - ys[i]
            a = 0
            while dy > dx:
                dy //= 2; a += 1
            while dy < dx:
                dx //= 2; a -= 1
            assert (ys[i + 1] - ys[i]) == mul2(xs[i + 1] - xs[i], a), "slope not power of 2"
            self.a.append(a)

    def g(self, x):
        xs = self.xs
        assert xs[0] <= x < xs[-1]
        lo, hi = 0, len(xs) - 2
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if xs[mid] <= x:
                lo = mid
            else:
                hi = mid - 1
        i = lo
        a = self.a[i]
        return self.ys[i] + mul2(x - xs[i], a), a, xs[i + 1] - x

    def inv(self):
        return RPL(self.ys, self.xs)


class Chain:
    def __init__(self, d_xs, d_ys, X, s0_xs, s0_ys):
        self.d = RPL([fx(*v) for v in d_xs], [fx(*v) for v in d_ys])
        self.dinv = self.d.inv()
        self.d0 = self.d.ys[0]
        self.X = fx(*X)
        self.s0 = RPL([fx(*v) for v in s0_xs], [fx(*v) for v in s0_ys])
        self.s0inv = self.s0.inv()
        self.Y = self.s0.ys[0]
        self.dX = self.delta(self.X)[0]
        self.ddY = self.delta(self.delta(self.Y)[0])[0]
        assert self.s0.xs[-1] == self.dX and self.s0.ys[-1] == self.ddY

    def delta(self, x):
        n = x >> E  # floor
        y, a, r = self.d.g(x - (n << E))
        return 2 * (n << E) + y, a, r

    def delta_inv(self, y):
        n = (y - self.d0) >> (E + 1)
        x, a, r = self.dinv.g(y - 2 * (n << E))
        return (n << E) + x, a, r

    def s(self, x):
        n, A, r = 0, 0, None
        while x >= self.dX:
            x, a1, r1 = self.delta_inv(x)
            r = _mn(r, ext_div(r1, A)); A += a1; n += 1
        y, a1, r1 = self.s0.g(x)
        r = _mn(r, ext_div(r1, A)); A += a1
        for _ in range(2 * n):
            y, a1, r1 = self.delta(y)
            r = _mn(r, ext_div(r1, A)); A += a1
        return y, A, r

    def s_inv(self, y):
        n, A, r = 0, 0, None
        while y >= self.ddY:
            for _ in range(2):
                y, a1, r1 = self.delta_inv(y)
                r = _mn(r, ext_div(r1, A)); A += a1
            n += 1
        x, a1, r1 = self.s0inv.g(y)
        r = _mn(r, ext_div(r1, A)); A += a1
        for _ in range(n):
            x, a1, r1 = self.delta(x)
            r = _mn(r, ext_div(r1, A)); A += a1
        return x, A, r


def T(c):
    return lambda x: (x + c, 0, None)


def comp(f, g):
    def h(x):
        y, ag, rg = g(x)
        z, af, rf = f(y)
        return z, af + ag, _mn(rg, ext_div(rf, ag))
    return h


def word(*fs):
    h = fs[-1]
    for f in reversed(fs[:-1]):
        h = comp(f, h)
    return h


def support(h, a, b):
    ivs, cur, x, npc = [], None, a, 0
    while x < b:
        y, s, r = h(x)
        npc += 1
        assert r is not None and r > 0, "extent underflow; raise E"
        end = min(x + r, b)
        if not (s == 0 and y == x):
            if cur is not None and cur[1] == x:
                cur[1] = end
            else:
                cur = [x, end]
                ivs.append(cur)
        x = x + r
    return ivs, npc


def nonaffine():
    return Chain([(0,), (1, 2), (3, 4), (1,)], [(1, 2), (1,), (3, 2), (5, 2)], (4,),
                 [(4,), (8,), (33, 4), (17, 2)], [(16,), (48,), (49,), (65,)])


def affine_control():
    return Chain([(0,), (1,)], [(0,), (2,)], (4,), [(4,), (6,), (8,)], [(16,), (32,), (64,)])


def elements(ch):
    s, si = ch.s, ch.s_inv
    tau = word(si, T(ONE), s)
    taui = word(si, T(-ONE), s)
    c1 = word(tau, T(ONE), taui, T(-ONE))
    c1i = word(T(ONE), tau, T(-ONE), taui)
    return dict(tau=tau, taui=taui, c1=c1, c1i=c1i)


def wk(ch, k):
    e = elements(ch)
    K = k * ONE
    ck = word(T(K), e['c1'], T(-K))
    cki = word(T(K), e['c1i'], T(-K))
    return word(e['c1'], ck, e['c1i'], cki)


def f(v):
    return v / ONE
