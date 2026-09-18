"""Extend the conjugacy C rho_{-1-k}(x) C^-1 = rho_k(y), C rho_{-1-k}(y) C^-1 = rho_k(x)^-1
(C = [[0,1,-2],[1,1,-1],[1,0,0]], checked in lr_conjugacy.py) from F to Gamma.

Searches, for e = +-1, words f in F of length <= 6 with C Z_{-1-k} C^-1 = Z_k^e rho_k(f),
first numerically at k = 6, 7, 11, then confirms the survivor symbolically in k.
If found, C rho_{-1-k}(Gamma) C^-1 = rho_k(Gamma) and the whole pair (G, N) for -1-k is
SL_3(Z)-conjugate to the pair for k.
"""
import itertools
from sympy import Matrix, symbols, eye, simplify, zeros

k = symbols('k')
C = Matrix([[0, 1, -2], [1, 1, -1], [1, 0, 0]])


def X(kk): return Matrix([[1, -2, 3], [0, kk, -1 - 2 * kk], [0, 1, -2]])
def Y(kk): return Matrix([[-2 - kk, -1, 1], [-2 - kk, -2, 3], [-1, -1, 2]])
def Z(kk): return Matrix([[0, 0, 1], [1, 0, -kk], [0, 1, -1 - kk]])


def word(kk, w):
    g = {'x': X(kk), 'X': X(kk).inv(), 'y': Y(kk), 'Y': Y(kk).inv()}
    M = eye(3)
    for c in w:
        M = M * g[c]
    return M


def reduced_words(n):
    for p in itertools.product('xXyY', repeat=n):
        w = ''.join(p)
        if all(w[i] != w[i + 1].swapcase() for i in range(n - 1)):
            yield w


def main():
    print('det C =', C.det())
    found = []
    for e in (1, -1):
        for n in range(0, 7):
            for w in reduced_words(n):
                ok = True
                for kk in (6, 7, 11):
                    lhs = C * Z(-1 - kk) * C.inv()
                    rhs = (Z(kk) if e == 1 else Z(kk).inv()) * word(kk, w)
                    if lhs != rhs:
                        ok = False
                        break
                if ok:
                    found.append((e, w))
            if found:
                break
        if found:
            break
    print('numeric candidates (e, f):', found)
    for e, w in found:
        lhs = C * Z(-1 - k) * C.inv()
        rhs = (Z(k) if e == 1 else Z(k).inv()) * word(k, w)
        print('symbolic check e=%d f=%s:' % (e, w), simplify(lhs - rhs) == zeros(3, 3))


if __name__ == '__main__':
    main()
