#!/usr/bin/env python3
"""Check of the seed derivation (S0) in the Fock model V = F_p[b]/(b^p) (x) F_p[eps]/(eps^3).

For the ab edge, u(<a,b,E13>) m0 = V with b = E23 acting by multiplication, eps = E13 central and
a = E12 acting as eps*D (D = d/db), since a m0 = 0.  For the bc edge, eps' = E21 t and c = E31 t acts as
-eps'*D, since c m0 = 0.  The relators are those of fo_dual.cpp (gexp = truncated exponential):
  [a,b,a]: C^-1 E(-a) C E(a) - 1,  C = E(-a)E(-b)E(a)E(b)
  [b,c,c]: C^-1 E(-c) C E(c) - 1,  C = E(-b)E(-c)E(b)E(c)
The script applies them to 1 and prints the coefficient vector of eps^2 (the multidegree (2,p,0) resp.
(0,p,2) component is eps^2 b^(p-2)).  Expected: X_210 = +b^(p-2) eps^2, X_012 = -b^(p-2) eps'^2.
Usage: python3 seed_derive.py p [p ...]
"""
import sys


def run(p):
    inv = lambda x: pow(x % p, p - 2, p)
    fact = [1] * p
    for i in range(1, p):
        fact[i] = fact[i - 1] * i % p
    finv = [inv(f) for f in fact]
    # vector: dict k -> list of p coefficients (poly in b), k = eps-degree 0..2
    def zero():
        return {k: [0] * p for k in range(3)}

    def mulpoly(f, g):
        h = [0] * p
        for i, x in enumerate(f):
            if x:
                for j, y in enumerate(g[: p - i]):
                    h[i + j] = (h[i + j] + x * y) % p
        return h

    def D(f):
        return [(i + 1) * f[i + 1] % p for i in range(p - 1)] + [0]

    ebeta = [finv[j] for j in range(p)]
    ebeta_inv = [finv[j] * (-1) ** j % p for j in range(p)]

    def mult(v, f):
        return {k: mulpoly(v[k], f) for k in v}

    def E_der(v, s):  # E(s*eps*D) = 1 + s eps D + s^2 eps^2 D^2 / 2, truncated at eps^3
        w = zero()
        for k in range(3):
            f = v[k]
            g = f
            for m in range(3 - k):
                c = pow(s, m, p) * finv[m] % p
                w[k + m] = [(x + c * y) % p for x, y in zip(w[k + m], g)]
                g = D(g)
        return w

    one = zero(); one[0][0] = 1
    # [a,b,a]: rightmost acts first.  a -> +eps D ; E(a)=E_der(+1), E(-a)=E_der(-1); b -> mult ebeta
    A = lambda v: E_der(v, 1); Ai = lambda v: E_der(v, -1)
    B = lambda v: mult(v, ebeta); Bi = lambda v: mult(v, ebeta_inv)
    # C^-1 E(-a) C E(a) = (B^-1 A^-1 B A) A^-1 (A^-1 B^-1 A B) A
    ops =['Bi', 'Ai', 'B', 'A', 'Ai', 'Ai', 'Bi', 'A', 'B', 'A']  # word left-to-right
    table = {'A': A, 'Ai': Ai, 'B': B, 'Bi': Bi}
    v = one
    for o in reversed(ops):
        v = table[o](v)
    x210 = v[2]
    # [b,c,c]: c -> -eps' D ; E(c) = E_der(-1), E(-c) = E_der(+1)
    Cc = lambda v: E_der(v, -1); Cci = lambda v: E_der(v, 1)
    table2 = {'A': Cc, 'Ai': Cci, 'B': B, 'Bi': Bi}
    # C = E(-b)E(-c)E(b)E(c) ; C^-1 = E(-c)E(-b)E(c)E(b) ; word C^-1 E(-c) C E(c)
    ops2 = ['Ai', 'Bi', 'A', 'B', 'Ai', 'Bi', 'Ai', 'B', 'A', 'A']
    v2 = one
    for o in reversed(ops2):
        v2 = table2[o](v2)
    x012 = v2[2]
    ok1 = x210 == [1 if j == p - 2 else 0 for j in range(p)] and v[1] == [0] * p and v[0] == [1] + [0] * (p - 1)
    ok2 = x012 == [(p - 1) if j == p - 2 else 0 for j in range(p)] and v2[1] == [0] * p and v2[0] == [1] + [0] * (p - 1)
    print(f"p={p} X_210 eps^2-part {x210} {'OK' if ok1 else 'FAIL'} ; X_012 eps'^2-part {x012} {'OK' if ok2 else 'FAIL'}")


for a in sys.argv[1:] or ['5', '7', '11', '13', '17', '19', '23']:
    run(int(a))
