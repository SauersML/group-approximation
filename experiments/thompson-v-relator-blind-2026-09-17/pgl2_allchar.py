"""Hom(G0/<<r>>, PGL(2, Fbar_p)) for r = r5, r8 and every prime p >= 5, via norms and resultants.

For p >= 5 the normal form of pgl2c_exact.py is valid over Fbar_p (a = diag(1,-1) needs p != 2;
the S3 pair needs xy = 3 != 0, and the order-3 and order-4 elements are semisimple for p != 2,3).
Every nontrivial map is conjugate to one with b in {OCT+, OCT-, S3, TRIV} and c in {c_t : t != 0} or
c = a.  OCT- is the Galois conjugate of OCT+ (sqrt(-2) -> -sqrt(-2)).

For each class we have f_1, f_2, f_3 in Z[1/2, sqrt(-2)][t] (entries M12, M21, M11-M22 of r(a,b,c_t)).
Put N_i = f_i * conj(f_i) in Z[1/2][t], stripped of powers of t.  A solution t0 != 0 over Fbar_p
(p odd) makes every N_i vanish at t0 mod p.  So if the N_i have no common root mod p, there is no
solution for that class at p.  Over Q we check gcd(N_1, N_2, N_3) = 1; then the primes where a
common root can appear divide R = gcd of the pairwise resultants (times the leading coefficients).
Each such prime >= 5 is then tested directly by gcd over GF(p).  The c = a case is a finite check
(the image is the S4-image, a finite group of order <= 24) done by the permutation census.
"""
import sys, math
import sympy as sp
sys.path.insert(0, 'experiments/thompson-v-models')
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
from census import load, word_str  # noqa: E402
from pgl2c_exact import a, bclasses, adj, word_matrix, t, r2  # noqa: E402


def conj(expr):
    return sp.expand(expr.subs(sp.I, -sp.I))   # sqrt(-2) = sqrt(2)*I; Galois conj = complex conj


def strip_t(P):
    while P.degree() > 0 and P.eval(0) == 0:
        P = sp.Poly(sp.quo(P.as_expr(), t), t)
    return P


def int_poly(expr):
    P = sp.Poly(sp.expand(expr), t, domain=sp.QQ)
    den = 1
    for c in P.coeffs():
        den = sp.ilcm(den, sp.fraction(c)[1])
    P = sp.Poly(sp.expand(P.as_expr() * den), t, domain=sp.ZZ)
    CONTENTS.append(int(P.primitive()[0]))   # primes dividing a content kill that equation mod p
    return strip_t(P.primitive()[1])


CONTENTS = []


def main():
    Rw = [word_str(w) for w in load('experiments/thompson-v-models/rel_V.txt')]
    ct = sp.Matrix([[t, t ** 2], [3, -t]])
    report = []
    for ri, name in ((0, 'r5'), (3, 'r8')):
        for bn in ('OCT+1', 'S3', 'TRIV'):
            b = bclasses[bn]
            M = word_matrix(Rw[ri], {'a': a, 'b': b, 'B': adj(b), 'c': ct})
            fs = [M[0, 1], M[1, 0], sp.expand(M[0, 0] - M[1, 1])]
            Ns = [int_poly(f * conj(f)) if bn == 'OCT+1' else int_poly(f) for f in fs]
            Ns = [N for N in Ns if not N.is_zero]
            g = Ns[0]
            for N in Ns[1:]:
                g = sp.gcd(g, N)
            assert g.degree() == 0, (name, bn, g)
            R = 0
            for i in range(len(Ns)):
                for j in range(i + 1, len(Ns)):
                    R = math.gcd(R, int(sp.resultant(Ns[i].as_expr(), Ns[j].as_expr(), t)))
            L = math.prod(int(N.LC()) for N in Ns)
            content_primes = set()
            for cc in CONTENTS[-3:]:
                content_primes |= set(sp.factorint(cc).keys())
            cand = sorted(set(sp.factorint(R).keys()) | set(sp.factorint(L).keys()) | content_primes) if R else None
            print('   contents', CONTENTS[-3:], flush=True)
            bad = []
            for p in (cand or []):
                if p < 5:
                    continue
                gp = sp.Poly(Ns[0].as_expr(), t, modulus=p)
                for N in Ns[1:]:
                    gp = sp.gcd(gp, sp.Poly(N.as_expr(), t, modulus=p))
                while gp.degree() > 0 and gp.eval(0) % p == 0:
                    gp = sp.Poly(sp.quo(gp.as_expr(), t), t, modulus=p)
                if gp.degree() > 0:
                    bad.append((p, str(gp.as_expr())))
            report.append((name, bn, [N.degree() for N in Ns], R, cand, bad))
            print(name, bn, 'deg', [N.degree() for N in Ns], 'gcd-resultant', R,
                  'candidate primes', cand, 'primes>=5 with a common root of the norms:', bad, flush=True)
    return report


if __name__ == '__main__':
    main()
