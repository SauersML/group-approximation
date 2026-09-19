# Twisted Fox vector of c_H over Z[t^+-1] for the characters psi: J -> Z that kill N.
# If c_H = [q] with q in N primitive in F_4, then q is primitive in J, and the vector
# c(t) = (psi(d U / d g_i))_i must be a unimodular row over Z[t^+-1] (Lemma B of the proof).
import sys
from sympy import symbols, gcd, factor, expand, Poly, groebner, S as SS
from common import *
from lattice import hnf
from coker import analyse

t = symbols('t')

def kernel_character(Lam, n):
    """Primitive integer vectors psi with psi . v = 0 for all v in Lam (rank n - rank Lam)."""
    from sympy import Matrix
    K = Matrix(Lam).nullspace()
    out = []
    for k in K:
        den = 1
        for x in k: den = den * x.q // gcd(den, x.q)
        v = [int(x * den) for x in k]
        g = 0
        for x in v: g = gcd(g, x)
        out.append([x // int(g) for x in v])
    return out

def fox_twisted(sg, u, psi):
    vec = [SS(0)] * sg.rank; s = 0
    for i, e in sg.rewrite(u):
        if e == 1:
            vec[i] += t ** s; s += psi[i]
        else:
            s -= psi[i]; vec[i] -= t ** s
    assert s == 0
    return [expand(v) for v in vec]

def report(act, b):
    sg, Lam, cH, inv_, _ = analyse(act, b)
    chars = kernel_character(Lam, sg.rank)
    for psi in chars:
        for w in N0.values():
            assert sum(a * c for a, c in zip(psi, sg.ab(w))) == 0
        c = fox_twisted(sg, U, psi)
        nz = [v for v in c if v != 0]
        g = SS(0)
        for v in nz: g = gcd(g, v)
        print('psi =', psi)
        print('  nonzero entries of c(t):', len(nz), '  gcd over Q[t]:', factor(g))
        print('  c(t) =', {sg.gens[i]: v for i, v in enumerate(c) if v != 0})
        # ideal generated over Z[t]: groebner basis over the integers is not in sympy;
        # report the content and the resultant-style test modulo small primes instead
        # (the factor t^200 only clears negative powers; it is a unit in Z[t^+-1]).
        for p in [2, 3, 5, 7]:
            gp = Poly(0, t, modulus=p)
            for v in nz:
                gp = gp.gcd(Poly(expand(v * t ** 200), t, modulus=p))
            print('   mod', p, 'gcd:', gp.as_expr())
    return sg, chars

if __name__ == '__main__':
    report(S9(), 4)
