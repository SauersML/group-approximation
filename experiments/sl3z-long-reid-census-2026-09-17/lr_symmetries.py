"""Symmetries of the Long-Reid representations rho_k.

(1) Reversal anti-involution: find J with J X^T = X J and J Y^T = Y J (symbolic in k).
    Then rho_k(rev(w)) = J rho_k(w)^T J^-1, so palindromes a.rev(a) map to S J^-1 with
    S = A J A^T.
(2) k -> -1-k: test whether rho_{-1-k}(x), rho_{-1-k}(y) is conjugate to rho_k of a
    fixed automorphism image (by comparing traces of many words).
"""
import itertools
from sympy import Matrix, symbols, eye, factor, simplify, zeros, solve, expand

k = symbols('k')


def X(k): return Matrix([[1, -2, 3], [0, k, -1 - 2 * k], [0, 1, -2]])
def Y(k): return Matrix([[-2 - k, -1, 1], [-2 - k, -2, 3], [-1, -1, 2]])
def Z(k): return Matrix([[0, 0, 1], [1, 0, -k], [0, 1, -1 - k]])


def reversal():
    js = symbols('j0:9')
    J = Matrix(3, 3, js)
    eqs = list(J * X(k).T - X(k) * J) + list(J * Y(k).T - Y(k) * J)
    sol = solve(eqs, js, dict=True)
    print('reversal anti-involution solutions:', sol)
    if sol:
        Js = J.subs(sol[0])
        print('J =', Js, ' det =', factor(Js.det()), ' symmetric:', simplify(Js - Js.T) == zeros(3, 3))
        # also z: J Z^T = Z^-1 J ?
        free = [s for s in js if s in Js.free_symbols]
        print('free params', free)
        print('J Z^T vs Z^-1 J difference zero:', simplify(Js * Z(k).T - Z(k).inv() * Js) == zeros(3, 3),
              ' J Z^T vs Z J:', simplify(Js * Z(k).T - Z(k) * Js) == zeros(3, 3))
    return sol


def word(kk, w):
    g = {'x': X(kk), 'y': Y(kk)}
    M = eye(3)
    for c in w:
        M = M * (g[c.lower()] if c.islower() else g[c.lower()].inv())
    return M


def sym_test(kk):
    """Look for a letter substitution s (images of x,y among short words) with
    tr rho_{-1-k}(w) = tr rho_k(s(w)) for all words of length <= 4."""
    words = [''.join(p) for n in range(1, 5) for p in itertools.product('xXyY', repeat=n)]
    subs_candidates = []
    short = [''.join(p) for n in (1, 2) for p in itertools.product('xXyY', repeat=n)]
    for sx in short:
        for sy in short:
            ok = True
            for w in words:
                img = ''.join({'x': sx, 'y': sy, 'X': sx[::-1].swapcase(), 'Y': sy[::-1].swapcase()}[c] for c in w)
                if word(-1 - kk, w).trace() != word(kk, img).trace():
                    ok = False
                    break
            if ok:
                subs_candidates.append((sx, sy))
    print('k=%d: substitutions s with tr rho_{-1-k}(w) = tr rho_k(s(w)) for |w|<=4:' % kk, subs_candidates)


if __name__ == '__main__':
    reversal()
    for kk in (3, 6):
        sym_test(kk)
