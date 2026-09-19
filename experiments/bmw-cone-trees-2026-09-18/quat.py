# The quaternion algebra D = [a, b) over K = F_2(t): i^2 = i + a, j^2 = b, j l = conj(l) j for l in L = K(i).
# Elements (c0, c1, c2, c3) = (c0 + c1 i) + (c2 + c3 i) j with c_k in F_2[t] (ints, see gf2poly).
from gf2poly import pmul, pgcd, pdivmod, val
class Quat:
    def __init__(self, a, b): self.a, self.b = a, b
    def lmul(self, x, y):                       # (x0 + x1 i)(y0 + y1 i)
        x0, x1 = x; y0, y1 = y
        z11 = pmul(x1, y1)
        return (pmul(x0, y0) ^ pmul(z11, self.a), pmul(x0, y1) ^ pmul(x1, y0) ^ z11)
    @staticmethod
    def lconj(x): return (x[0] ^ x[1], x[1])
    def mul(self, X, Y):
        l1, l2 = (X[0], X[1]), (X[2], X[3]); m1, m2 = (Y[0], Y[1]), (Y[2], Y[3])
        p = self.lmul(l1, m1); q = self.lmul(l2, self.lconj(m2)); q = (pmul(q[0], self.b), pmul(q[1], self.b))
        r = self.lmul(l1, m2); s = self.lmul(l2, self.lconj(m1))
        return (p[0] ^ q[0], p[1] ^ q[1], r[0] ^ s[0], r[1] ^ s[1])
    @staticmethod
    def conj(X): return (X[0] ^ X[1], X[1], X[2], X[3])       # X * conj(X) = Nrd(X)
    def lnorm(self, x): return pmul(x[0], x[0]) ^ pmul(x[0], x[1]) ^ pmul(pmul(x[1], x[1]), self.a)
    def nrd(self, X): return self.lnorm((X[0], X[1])) ^ pmul(self.b, self.lnorm((X[2], X[3])))
    @staticmethod
    def trd(X): return X[1]
    @staticmethod
    def norm(X):
        g = 0
        for x in X: g = pgcd(g, x)
        return tuple(pdivmod(x, g)[0] for x in X)
    @staticmethod
    def proj_eq(X, Y):
        for u in range(4):
            for w in range(4):
                if pmul(X[u], Y[w]) != pmul(X[w], Y[u]): return False
        return any(X) and any(Y)
    def dist(self, X, P):
        """distance moved by the standard vertex O_P<i,j> of the tree at the finite place P (a, b integral, b a unit at P)"""
        return val(self.nrd(X), P) - 2 * min(val(x, P) for x in X if x)
