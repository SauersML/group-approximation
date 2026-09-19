"""Bend-local pictures of the germs e0 = [sigma] and e1 = [rho sigma rho^-1] at +infinity.

In Lambda-coordinates y (x = 2^floor(y) * (1 + frac(y))) the germ generators are
  sigma = x+1  ->  e0 ,   delta = 2x -> y+1 ,   s = square map -> y -> 2y ,
  rho = s^-1 delta s -> y + 1/2 .
Coordinate 1 = picture at the integers   (w = 2^(m-1) (y - m)):      e0 -> eps, e1 -> T_1
Coordinate 2 = picture at the half-integers (w = 2^(n-1) (y - n - 1/2)): e0 -> T_1/2, e1 -> eps
"""
from pl import *

eps = make([-1, 0], [(1, 1), (Fr(1, 2), Fr(1, 2)), (1, Fr(1, 2))])
T1 = make([], [(1, 1)])
Th = make([], [(1, Fr(1, 2))])
A = (eps, Th)   # e0
B = (T1, eps)   # e1
I = (IDENT, IDENT)


def pm(*xs):
    return (mul(*[x[0] for x in xs]), mul(*[x[1] for x in xs]))


def pinv(x):
    return (inverse(x[0]), inverse(x[1]))


def pcomm(x, y):
    return pm(x, y, pinv(x), pinv(y))


def pw(x, n):
    r = I
    for _ in range(abs(n)):
        r = pm(r, x if n > 0 else pinv(x))
    return r


def span(f):
    s = support(f)
    return (s[0][0], s[-1][1]) if s else None


def f_relations(x0, x1):
    """The two Cannon-Floyd-Parry relators of F, and the commutator."""
    r1 = pcomm(pm(x0, pinv(x1)), pm(pinv(x0), x1, x0))
    r2 = pcomm(pm(x0, pinv(x1)), pm(pinv(x0), pinv(x0), x1, x0, x0))
    return r1 == I, r2 == I, pcomm(x0, x1) != I
