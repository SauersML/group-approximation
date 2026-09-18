#!/usr/bin/env python3
"""Exact model of the Soelberg group S and Gardam's unit of F_2[S] (pure python).

S = < x, y | (xy)^2 (xy^-1)^2, (yx)^2 (yx^-1)^2 >, torsion-free, virtually the integral
Heisenberg group (index 16), not virtually abelian (Gardam, arXiv:2312.05240v2, Section 4).
Faithful representation in GL_3(Z) taken verbatim from Gardam's ancillary file
verify_soelberg_unit.sage:
    x -> [[-1,1,0],[0,-1,0],[0,0,1]],   y -> [[1,0,0],[0,-1,1],[0,0,-1]].
Gardam's Theorem B: nu = sum(A) is a unit of F_2[S] with inverse sum(B), where A, B are the
29-element lists of words below (copied verbatim from the ancillary file; X = x^-1, Y = y^-1).
"""

def mmul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)) for i in range(3))

def minv(a):
    # integer matrices of determinant +-1
    (a0, a1, a2), (b0, b1, b2), (c0, c1, c2) = a
    det = a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)
    assert det in (1, -1)
    adj = ((b1 * c2 - b2 * c1, a2 * c1 - a1 * c2, a1 * b2 - a2 * b1),
           (b2 * c0 - b0 * c2, a0 * c2 - a2 * c0, a2 * b0 - a0 * b2),
           (b0 * c1 - b1 * c0, a1 * c0 - a0 * c1, a0 * b1 - a1 * b0))
    return tuple(tuple(det * v for v in row) for row in adj)

I3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
GX = ((-1, 1, 0), (0, -1, 0), (0, 0, 1))
GY = ((1, 0, 0), (0, -1, 1), (0, 0, -1))
GEN = {'x': GX, 'y': GY, 'X': minv(GX), 'Y': minv(GY)}

def word(w):
    """w is a string over x, y, X, Y, with optional ^n exponents on single letters, '*' separators."""
    g = I3
    for tok in w.split('*'):
        tok = tok.strip()
        if not tok:
            continue
        if '^' in tok:
            letter, n = tok.split('^')
            n = int(n)
        else:
            letter, n = tok, 1
        for _ in range(n):
            g = mmul(g, GEN[letter])
    return g

A_WORDS = ["x", "X", "y", "Y", "x*y", "X*Y", "y*X", "y^2", "Y*x", "Y^2", "x^2*y", "x*Y*x", "x*Y^2",
           "X^2*Y", "X*y*X", "X*y^2", "y*x*y", "Y*X*Y", "x^2*Y*x", "x*y*x^2", "X^2*y*X", "X*Y*X^2",
           "y*X^2*Y", "Y*x^2*y", "x^2*y*x^2", "x*Y*x^2*y", "X^2*Y*X^2", "X*y*X^2*Y", "x^2*Y*x^2*y"]
B_WORDS = ["Y", "y", "x", "X", "x*Y", "X*y", "y*x", "x^2", "Y*X", "X^2", "x*Y^2", "Y*X*Y", "X^2*Y",
           "X*y^2", "y*x*y", "x^2*y", "x*Y*x", "X*y*X", "Y*X*Y^2", "Y^2*x*Y", "y*x*y^2", "y^2*X*y",
           "X*y^2*x", "x*Y^2*X", "Y^2*x*Y^2", "x*Y^2*X*Y", "y^2*X*y^2", "X*y^2*x*y", "x*Y^2*X*Y^2"]
A = [word(w) for w in A_WORDS]
B = [word(w) for w in B_WORDS]

def relators_ok():
    x, y, X, Y = GEN['x'], GEN['y'], GEN['X'], GEN['Y']
    r1 = word("x*y*x*y*x*Y*x*Y")
    r2 = word("y*x*y*x*y*X*y*X")
    return r1 == I3 and r2 == I3

def product_table(S1, S2):
    """dict group element -> list of (i, j) with S1[i] S2[j] = element"""
    tab = {}
    for i, g in enumerate(S1):
        for j, h in enumerate(S2):
            tab.setdefault(mmul(g, h), []).append((i, j))
    return tab

def f2_unit_ok():
    tab = product_table(A, B)
    for g, pairs in tab.items():
        par = len(pairs) % 2
        if g == I3:
            if par != 1:
                return False
        elif par != 0:
            return False
    return True

def gmul_elems(u, v):
    """u, v: dict element -> coefficient (any ring with + and *)."""
    out = {}
    for g, a in u.items():
        for h, b in v.items():
            k = mmul(g, h)
            out[k] = out.get(k, 0) + a * b
    return {k: c for k, c in out.items() if c != 0}

if __name__ == '__main__':
    print('distinct A:', len(set(A)), 'distinct B:', len(set(B)))
    print('relators hold in the representation:', relators_ok())
    print('nu * nu_inv = 1 in F_2[S]:', f2_unit_ok())
    tab = product_table(A, B)
    print('number of product elements:', len(tab), ' pairs at identity:', len(tab[I3]))
