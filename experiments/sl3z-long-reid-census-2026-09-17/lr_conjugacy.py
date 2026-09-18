"""Exact check that rho_{-1-k}|F is conjugate in GL_3(Q(k)) to rho_k o s, where s is the
automorphism of F = <x, y> given by s(x) = y, s(y) = x^-1.
Hence rho_{-1-k}(F) and rho_k(F) are conjugate subgroups (in GL_3(Q); we also check
integrality/determinant of the conjugator), so the census needs only k >= 0.

Also tests the reversal involution: tr rho_k(rev w) == tr rho_k(w)?
"""
import itertools
from sympy import Matrix, symbols, eye, factor, solve, zeros, simplify

k = symbols('k')


def X(k): return Matrix([[1, -2, 3], [0, k, -1 - 2 * k], [0, 1, -2]])
def Y(k): return Matrix([[-2 - k, -1, 1], [-2 - k, -2, 3], [-1, -1, 2]])


def main():
    cs = symbols('c0:9')
    C = Matrix(3, 3, cs)
    eqs = list(C * X(-1 - k) - Y(k) * C) + list(C * Y(-1 - k) - X(k).inv() * C)
    sol = solve(eqs, cs, dict=True)
    print('solutions:', sol)
    Cs = C.subs(sol[0])
    print('C =', Cs)
    print('det C =', factor(Cs.det()))
    print('check C X_{-1-k} C^-1 == Y_k:', simplify(Cs * X(-1 - k) - Y(k) * Cs) == zeros(3, 3))
    print('check C Y_{-1-k} C^-1 == X_k^-1:', simplify(Cs * Y(-1 - k) - X(k).inv() * Cs) == zeros(3, 3))

    def word(kk, w):
        g = {'x': X(kk), 'y': Y(kk)}
        M = eye(3)
        for c in w:
            M = M * (g[c.lower()] if c.islower() else g[c.lower()].inv())
        return M
    for kk in (4, 5, 6):
        bad = 0
        for n in range(1, 6):
            for p in itertools.product('xXyY', repeat=n):
                w = ''.join(p)
                if word(kk, w).trace() != word(kk, w[::-1]).trace():
                    bad += 1
        print('k=%d: words |w|<=5 with tr(rev w) != tr(w):' % kk, bad)


if __name__ == '__main__':
    main()
