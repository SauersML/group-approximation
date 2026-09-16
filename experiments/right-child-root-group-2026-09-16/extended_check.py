"""Extended exact check (2026-09-16): the closed forms of b^-j s b^j for s in {y, x1, y1} (artifact Lemma 2) for
j <= 8, and for b^-j x b^j the least integer c such that every canonical monomial S[mu]T[nu] satisfies
w(mu) <= w(nu) for the weight w(0) = 1, w(1) = c.  Expected: c = max(j, 1), matching Lemma 3 and Remark 3.1.
Usage: python3 -B extended_check.py
"""
from leavitt_ops import *
x = ident_plus([('0', '10')]); y = ident_plus([('10', '11')])
x1 = ident_plus([('10', '110')]); y1 = ident_plus([('110', '111')])
b = monomial_sum([('0', '0'), ('100', '10'), ('11', '110'), ('101', '111')])
binv = monomial_sum([('0', '0'), ('10', '100'), ('110', '11'), ('111', '101')])
def phi_u(j):
    return ident_plus([('10', '11' + '0'*(2*j))] + [('11'+'0'*(j-1-i)+'1', '11'+'0'*(j+i)+'1') for i in range(j)])
def phi_x(j):
    return ident_plus([('10', '11' + '0'*(2*j+1))] + [('11'+'0'*(j-1-i)+'1', '11'+'0'*(j+1+i)+'1') for i in range(j)])
def phi_y(j):
    return ident_plus([('11'+'0'*(j+1), '11'+'0'*j+'1')])
def w(word, a, c): return a*word.count('0') + c*word.count('1')
hy, hx1, hy1, hx = y, x1, y1, x
J = 8
for j in range(J+1):
    if j > 0:
        hy = mul(mul(binv, hy), b); hx1 = mul(mul(binv, hx1), b); hy1 = mul(mul(binv, hy1), b); hx = mul(mul(binv, hx), b)
    assert key(hy) == key(phi_u(j)) and key(hx1) == key(phi_x(j)) and key(hy1) == key(phi_y(j)), j
    # b^-j x b^j: minimal c with all monomials w(mu) <= w(nu) for a = 1
    cmin = None
    for c in range(1, 20):
        if all(w(mu,1,c) <= w(nu,1,c) for nu, F in hx.items() for mu in F):
            cmin = c; break
    print('j=%d: closed forms ok; b^-j x b^j size %d, minimal integer weight c (a=1) = %s' % (j, size(hx), cmin), flush=True)
