"""Exact verification of the Long-Reid representations rho_k (Exp. Math. 20 (2011), Prop 2.1).

Gamma = < x, y, z | z x z^-1 = x y, z y z^-1 = y x y >, fibre F = <x, y> free of rank 2.
Checks: det = 1, both relations hold symbolically in k, factor det([X,Y]-I),
the stable-letter powers Z_0^10, Z_1^4, Z_2^3 versus the commutator, and X_3^6 = I.
"""
from sympy import Matrix, symbols, eye, factor, expand

k = symbols('k')


def X(k): return Matrix([[1, -2, 3], [0, k, -1 - 2 * k], [0, 1, -2]])
def Y(k): return Matrix([[-2 - k, -1, 1], [-2 - k, -2, 3], [-1, -1, 2]])
def Z(k): return Matrix([[0, 0, 1], [1, 0, -k], [0, 1, -1 - k]])


def word(kk, w):
    gens = {'x': X(kk), 'y': Y(kk), 'z': Z(kk)}
    M = eye(3)
    for c in w:
        g = gens[c.lower()]
        M = M * (g if c.islower() else g.inv())
    return M


def main():
    for f in (X, Y, Z):
        print(f.__name__, 'det =', factor(f(k).det()))
    r1 = (Z(k) * X(k) * Z(k).inv() - X(k) * Y(k)).applyfunc(expand)
    r2 = (Z(k) * Y(k) * Z(k).inv() - Y(k) * X(k) * Y(k)).applyfunc(expand)
    print('relation zxz^-1 = xy holds:', r1 == Matrix.zeros(3, 3))
    print('relation zyz^-1 = yxy holds:', r2 == Matrix.zeros(3, 3))
    C = word(k, 'xyXY').applyfunc(expand)
    print('det([X,Y]-I) =', factor((C - eye(3)).det()))
    for kk, n in ((0, 10), (1, 4), (2, 3)):
        Zn = Z(kk) ** n
        print('k=%d Z^%d == xyXY:' % (kk, n), Zn == word(kk, 'xyXY'),
              ' == XYxy:', Zn == word(kk, 'XYxy'),
              ' == yxYX:', Zn == word(kk, 'yxYX'),
              ' == YXyx:', Zn == word(kk, 'YXyx'),
              ' inverse forms:', Zn.inv() == word(kk, 'xyXY'), Zn.inv() == word(kk, 'XYxy'))
    print('X_3^6 == I:', X(3) ** 6 == eye(3), ' X_3^2,3 == I:', X(3) ** 2 == eye(3), X(3) ** 3 == eye(3))


if __name__ == '__main__':
    main()
