#!/usr/bin/env python3
"""Girths of the coset graphs of U_3(p) = <x,y | x^p, y^p, [x,y,x], [x,y,y]> and
U_4(p) = <x,y | x^p, y^p, [x,y,x], [x,y,y,x], [x,y,y,y]> with respect to <x>, <y>, for every odd prime p.

A backtrack-free closed walk of length 2n in the coset graph is an alternating relation
x^e1 y^f1 ... x^en y^fn = 1 with every exponent nonzero mod p.  Normal forms (see verify_integer_certificate.py):
  U_3: y^beta x^alpha u^mu, u = [x,y] central; law mu = mu1 + mu2 + alpha1*beta2.
  U_4: y^beta x^gamma u^mu v^nu, u = [x,y], v = [u,y] central; law
       mu = mu1 + mu2 + beta2*gamma1,  nu = nu1 + nu2 + gamma1*C(beta2,2) + beta2*mu1.
Exponents may be read mod p because u^p = v^p = 1 (proof node).  Checks, with exact polynomial arithmetic over Q:
  (A) U_3, n = 2: (alpha, beta, mu) of x^e1 y^f1 x^e2 y^f2 is (e1+e2, f1+f2, e1*f1 + (e1+e2)*f2).
  (B) U_4, n = 2: mu = e1*f1 + (e1+e2)*f2.
  (C) U_4, n = 3: under e3 = -e1-e2 and f3 = -f1-f2, the polynomial 2*nu + e3*f2*f3 is a multiple of mu.
  (D) explicit alternating integer relations of lengths 6 (U_3) and 8 (U_4) with exponents in {-2,-1,1,2}.
"""
from fractions import Fraction
from itertools import product

# --- tiny multivariate polynomials: dict monomial(tuple of 6 exponents for e1,f1,e2,f2,e3,f3) -> Fraction
V = 6
def P(c=0, var=None):
    if var is None: return {(0,) * V: Fraction(c)} if c else {}
    m = [0] * V; m[var] = 1; return {tuple(m): Fraction(1)}
def add(p, q, s=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + s * v
        if r[k] == 0: del r[k]
    return r
def mul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = tuple(a + b for a, b in zip(k1, k2)); r[k] = r.get(k, 0) + v1 * v2
            if r[k] == 0: del r[k]
    return r
def scal(p, c): return {k: v * c for k, v in p.items()} if c else {}
def C2(p): return scal(mul(p, add(p, P(1), -1)), Fraction(1, 2))
e = [P(var=0), P(var=2), P(var=4)]; f = [P(var=1), P(var=3), P(var=5)]

def u4_word(n):
    beta, gamma, mu, nu = P(), P(), P(), P()
    for i in range(n):
        gamma = add(gamma, e[i])                                  # times x^e_i (beta2 = 0)
        b2 = f[i]                                                 # times y^f_i
        mu, nu = add(add(mu, mul(b2, gamma)), P()), add(add(nu, mul(gamma, C2(b2))), mul(b2, mu))
        beta = add(beta, b2)
    return beta, gamma, mu, nu
def u3_word(n):
    beta, alpha, mu = P(), P(), P()
    for i in range(n):
        alpha = add(alpha, e[i]); mu = add(mu, mul(alpha, f[i])); beta = add(beta, f[i])
    return beta, alpha, mu

def subst(p, rules):
    """substitute variables by polynomials"""
    out = {}
    for mon, c in p.items():
        term = P(c)
        for var, d in enumerate(mon):
            base = rules.get(var, P(var=var))
            for _ in range(d): term = mul(term, base)
        out = add(out, term)
    return out
def divides(num, den):
    """exact division of polynomials in the variables e1,f1,e2,f2 by den, lex long division; returns (quotient, remainder)"""
    order = lambda m: m                                           # lexicographic monomial order
    q, r = {}, dict(num)
    lead_d = max(den, key=order)
    while r:
        lm = max(r, key=order)
        if all(a >= b for a, b in zip(lm, lead_d)):
            mon = tuple(a - b for a, b in zip(lm, lead_d)); c = r[lm] / den[lead_d]
            q = add(q, {mon: c}); r = add(r, mul({mon: c}, den), -1)
        else:
            return q, r
    return q, r

print("(A) U_3 n=2 normal form:", u3_word(2))
b, g, m, n = u4_word(2); print("(B) U_4 n=2: mu =", m)
b, g, m, n = u4_word(3)
rules = {4: add(scal(e[0], -1), e[1], -1), 5: add(scal(f[0], -1), f[1], -1)}
mu3 = subst(m, rules); nu3 = subst(n, rules)
target = add(scal(nu3, 2), mul(rules[4], mul(f[1], rules[5])))
quo, rem = divides(target, mu3)
print("(C) U_4 n=3 after E=F=0: mu =", mu3)
print("    2*nu + e3*f2*f3 = (quotient)*mu with remainder", rem, "| quotient", quo)

# (D) explicit relations, evaluated with the integer laws
def n3_eval(word):                    # word: list of (letter, exponent), letter 'x' or 'y'
    beta = alpha = mu = 0
    for letter, x in word:
        if letter == 'x': alpha += x
        else: mu += alpha * x; beta += x
    return (beta, alpha, mu)
def n4_eval(word):
    beta = gamma = mu = nu = 0
    for letter, x in word:
        if letter == 'x': gamma += x
        else: nu += gamma * x * (x - 1) // 2 + x * mu; mu += x * gamma; beta += x
    return (beta, gamma, mu, nu)
vals = [-2, -1, 1, 2]
six = next(w for w in product(vals, repeat=6) if n3_eval([('x', w[0]), ('y', w[1]), ('x', w[2]), ('y', w[3]), ('x', w[4]), ('y', w[5])]) == (0, 0, 0))
eight = next(w for w in product(vals, repeat=8) if n4_eval([(('x', 'y')[i % 2], w[i]) for i in range(8)]) == (0, 0, 0, 0))
print("(D) length-6 relation in U_3 over Z: x^%d y^%d x^%d y^%d x^%d y^%d" % six)
print("    length-8 relation in U_4 over Z: x^%d y^%d x^%d y^%d x^%d y^%d x^%d y^%d" % eight)
ok = (rem == {})
print("PASS" if ok else "FAIL")
