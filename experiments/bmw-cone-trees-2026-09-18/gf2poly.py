# polynomials over F_2 as Python ints (bit i = coefficient of t^i)
def pmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def pdeg(a): return a.bit_length() - 1
def pdivmod(a, b):
    q = 0; db = pdeg(b)
    while a and pdeg(a) >= db:
        s = pdeg(a) - db; q ^= 1 << s; a ^= b << s
    return q, a
def pgcd(a, b):
    while b: a, b = b, pdivmod(a, b)[1]
    return a
def val(a, P):
    """valuation of polynomial a at place P: P=0 -> t, P=1 -> t+1, P='inf' -> -deg; a != 0"""
    if P == 'inf': return -pdeg(a)
    p = 2 if P == 0 else 3 if P == 1 else P      # P >= 2: the irreducible polynomial P itself
    v = 0
    while True:
        q, r = pdivmod(a, p)
        if r: return v
        a = q; v += 1
def mmul(X, Y):
    a, b, c, d = X; e, f, g, h = Y
    return (pmul(a, e) ^ pmul(b, g), pmul(a, f) ^ pmul(b, h), pmul(c, e) ^ pmul(d, g), pmul(c, f) ^ pmul(d, h))
def mdet(X): a, b, c, d = X; return pmul(a, d) ^ pmul(b, c)
def madj(X): a, b, c, d = X; return (d, b, c, a)          # inverse up to the scalar det (char 2)
def mnorm(X):
    g = 0
    for x in X: g = pgcd(g, x)
    return tuple(pdivmod(x, g)[0] for x in X)
def proj_eq(X, Y):
    for i in range(4):
        for j in range(4):
            if pmul(X[i], Y[j]) != pmul(X[j], Y[i]): return False
    return any(X) and any(Y)
def dist(X, P):
    """distance from the standard vertex to X.(standard vertex) in the Bruhat-Tits tree at P"""
    return val(mdet(X), P) - 2 * min(val(x, P) for x in X if x)
