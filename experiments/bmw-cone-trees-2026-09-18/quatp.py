# Quaternion algebra (a, b) over F_p(t), p odd: i^2 = a, j^2 = b, k = ij = -ji.
# Elements are 4-tuples of polynomials (fpoly tuples) x0 + x1 i + x2 j + x3 k.
import fpoly as F
class QuatP:
    def __init__(self, a, b): self.a, self.b = a, b; self.ab = F.mul(a, b)
    def mul(self, X, Y):
        a, b, ab = self.a, self.b, self.ab; m = F.mul; ad = F.add; sb = F.sub
        x0, x1, x2, x3 = X; y0, y1, y2, y3 = Y
        r0 = sb(ad(ad(m(x0, y0), m(a, m(x1, y1))), m(b, m(x2, y2))), m(ab, m(x3, y3)))
        r1 = ad(ad(m(x0, y1), m(x1, y0)), m(b, sb(m(x3, y2), m(x2, y3))))
        r2 = ad(ad(m(x0, y2), m(x2, y0)), m(a, sb(m(x1, y3), m(x3, y1))))
        r3 = ad(ad(m(x0, y3), m(x3, y0)), sb(m(x1, y2), m(x2, y1)))
        return (r0, r1, r2, r3)
    @staticmethod
    def conj(X): return (X[0], F.neg(X[1]), F.neg(X[2]), F.neg(X[3]))
    def nrd(self, X):
        m = F.mul; x0, x1, x2, x3 = X
        return F.add(F.sub(F.sub(m(x0, x0), m(self.a, m(x1, x1))), m(self.b, m(x2, x2))), m(self.ab, m(x3, x3)))
    @staticmethod
    def norm(X):
        g = ()
        for x in X: g = F.gcd(g, x) if g else F.monic(x) if x else g
        Y = tuple(F.divmod_(x, g)[0] for x in X)
        lead = next(y[-1] for y in Y if y)
        return tuple(F.smul(pow(lead, F.P - 2, F.P), y) for y in Y)
    @staticmethod
    def proj_eq(X, Y):
        for u in range(4):
            for w in range(u + 1, 4):
                if F.sub(F.mul(X[u], Y[w]), F.mul(X[w], Y[u])): return False
        return any(X) and any(Y)
    def dist(self, X, pl):
        return F.val(self.nrd(X), pl) - 2 * min(F.val(x, pl) for x in X if x)
def ramification(a, b, irr):
    """finite places (from irr) where (a, b) ramifies, and whether infinity ramifies (product formula)"""
    R = []
    for pl in irr:
        al, be = F.val(a, pl), F.val(b, pl)
        if al == 0 and be == 0: continue
        a0 = a; b0 = b
        for _ in range(al): a0 = F.divmod_(a0, pl)[0]
        for _ in range(be): b0 = F.divmod_(b0, pl)[0]
        s = (F.legendre((F.P - 1,), pl) ** (al * be)) * (F.legendre(a0, pl) ** be) * (F.legendre(b0, pl) ** al)
        if s == -1: R.append(pl)
    return R, len(R) % 2 == 1
