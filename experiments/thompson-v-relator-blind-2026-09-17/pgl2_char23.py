"""Hom(G0/<<r>>, PGL(2, Fbar_p)) for p = 2, 3 and r in {r5, ..., r8}: exact, by one-variable gcds.

Completes pgl2_allchar.py (char 0 and char >= 5).  G0 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>.
A map is nontrivial iff a maps nontrivially (a -> 1 forces b^4 = b^3 = 1 and c^3 = c^2 = 1).
The maps with b -> 1 or c -> a have image a quotient of S3 or of S4, a finite group acting
faithfully on <= 4 points; these are covered by the permutation census (census.py, log_m16.txt).
So only b != 1, c != a remain, and then:

char 3.  a = diag(1,-1) (involutions are semisimple, all conjugate).  ac has order 3, hence is
  unipotent: for c = [[al,be],[ga,-al]], tr(ac)^2 = 4 det(ac) gives be*ga = 0, and det c != 0
  gives al != 0 = scale al = 1.  The torus diag(t,1) and the swap [[0,1],[1,0]] (both centralise a)
  bring c to cU = [[1,1],[0,-1]], with trivial residual stabiliser in the torus.  b has order 3,
  so is unipotent: scale tr b = 2, det b = 1, b = [[1+u, y],[z, 1-u]] with u^2 + yz = 0.  Then
  tr(ab) = 2u, det(ab) = -1, and ab of order 2 or 4 means tr(ab)^2 = 0 or 2 det(ab), i.e. u = 0
  or u^2 = -1/2 = 1.  Families:
    U+ / U- : u = +-1, z = -1/y, projectively b ~ [[(1+u)y, y^2], [-1, (1-u)y]], y != 0;
    N1      : u = 0, z = 0, b = [[1, y], [0, 1]], y != 0;
    N2      : u = 0, y = 0, b = [[1, 0], [y, 1]], y != 0.
char 2.  PGL(2) = SL(2).  a is unipotent, a = [[1,1],[0,1]].  There are no elements of order 4,
  so (ab)^4 = 1 forces (ab)^2 = 1 (the S4-image is S3).  c = [[x,y],[z,x]] with x^2 + yz = 1;
  tr(ac) = z must be 1 (order 3 in SL(2)), and the unipotent centraliser [[1,s],[0,1]] of a shifts
  x -> x + s, so c = [[0,1],[1,0]] with trivial residual stabiliser.  b: tr b = 1, det b = 1,
  tr(ab) = 0 gives b = [[q, q^2+q+1], [1, 1+q]], one free parameter q.
In each family the relator r gives polynomials M12, M21, M11 - M22 in F_p[y] (resp. F_p[q]).
A solution over Fbar_p is a common root (y != 0 in char 3).  gcd over F_p = gcd over Fbar_p.
Controls: the words (bc)^5, (bc)^7 must have solutions (bc of order 5 or 7 exists).
"""
import sys, itertools
import sympy as sp
sys.path.insert(0, 'experiments/thompson-v-models')
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
from census import load, word_str  # noqa: E402

y = sp.symbols('y')


def adj(M):
    return sp.Matrix([[M[1, 1], -M[0, 1]], [-M[1, 0], M[0, 0]]])


def wmat(w, gens, p):
    M = sp.eye(2)
    for ch in w:
        M = (M * gens[ch]).applyfunc(lambda e: sp.Poly(sp.expand(e), y, modulus=p).as_expr())
    return M


def scalar_polys(M, p):
    return [sp.Poly(M[0, 1], y, modulus=p), sp.Poly(M[1, 0], y, modulus=p),
            sp.Poly(sp.expand(M[0, 0] - M[1, 1]), y, modulus=p)]


def is_scalar(M, p):
    return all(P.is_zero for P in scalar_polys(M, p))


def families():
    fam = {}
    a3 = sp.Matrix([[1, 0], [0, -1]])
    c3 = sp.Matrix([[1, 1], [0, -1]])
    for u in (1, -1):
        fam['char3 U%+d' % u] = (3, a3, sp.Matrix([[(1 + u) * y, y ** 2], [-1, (1 - u) * y]]), c3, True)
    fam['char3 N1'] = (3, a3, sp.Matrix([[1, y], [0, 1]]), c3, True)
    fam['char3 N2'] = (3, a3, sp.Matrix([[1, 0], [y, 1]]), c3, True)
    a2 = sp.Matrix([[1, 1], [0, 1]])
    c2 = sp.Matrix([[0, 1], [1, 0]])
    fam['char2'] = (2, a2, sp.Matrix([[y, y ** 2 + y + 1], [1, 1 + y]]), c2, False)
    return fam


def solve(w, p, gens, nonzero):
    g = sp.Poly(0, y, modulus=p)
    for P in scalar_polys(wmat(w, gens, p), p):
        g = sp.gcd(g, P)
    if g.is_zero:
        return 'identically'
    if nonzero:
        while g.degree() > 0 and g.eval(0) % p == 0:
            g = sp.Poly(sp.quo(g.as_expr(), y), y, modulus=p)
    return 'none' if g.degree() <= 0 else 'deg %d: %s' % (g.degree(), g.as_expr())


def main():
    Rw = [word_str(w) for w in load('experiments/thompson-v-models/rel_V.txt')]
    names = ['r5', 'r6', 'r7', 'r8']
    for fname, (p, a, b, c, nonzero) in families().items():
        gens = {'a': a, 'b': b, 'B': adj(b), 'c': c}
        # the defining relations of G0 hold identically in the family
        for w in ('aa', 'bbb', 'abababab', 'cc', 'acacac'):
            assert is_scalar(wmat(w, gens, p), p), (fname, w)
        # a != 1, b != 1, c != a in PGL for every admissible parameter (checked generically)
        assert not is_scalar(a, p) and not is_scalar(b, p)
        print(fname, 'controls: (bc)^5 ->', solve('bc' * 5, p, gens, nonzero),
              '| (bc)^7 ->', solve('bc' * 7, p, gens, nonzero), flush=True)
        single = {}
        for i, w in enumerate(Rw):
            single[i] = solve(w, p, gens, nonzero)
            print('   ', fname, names[i], '->', single[i], flush=True)
        for r in (2, 3, 4):
            for S in itertools.combinations(range(4), r):
                g = sp.Poly(0, y, modulus=p)
                for i in S:
                    for P in scalar_polys(wmat(Rw[i], gens, p), p):
                        g = sp.gcd(g, P)
                if nonzero:
                    while not g.is_zero and g.degree() > 0 and g.eval(0) % p == 0:
                        g = sp.Poly(sp.quo(g.as_expr(), y), y, modulus=p)
                lab = '{' + ','.join(names[i] for i in S) + '}'
                desc = 'identically' if g.is_zero else ('none' if g.degree() <= 0 else 'deg %d' % g.degree())
                print('   ', fname, lab, '->', desc, flush=True)


if __name__ == '__main__':
    main()
