"""Exact determination of Hom(G0/<<S>>, PGL(2,C)) for every subset S of {r5,r6,r7,r8}.

Normal form (PGL(2,C) = PSL(2,C); a GL matrix is trivial iff it is scalar):
  a = diag(1,-1).  A nontrivial map sends a to an involution, all conjugate.
  c: an involution with (ac)^3 = 1 in PGL, i.e. c = [[1,x],[y,-1]] with xy = 3,
     or c = a (degenerate S3-image Z2).  Conjugating by the centralizer diag(t,1)
     of a gives c_t = [[1,t],[3/t,-1]] ~ [[t,t^2],[3,-t]], t in C^*.
  b: after using the centralizer on c we may NOT normalise b again, so we
     normalise b first instead and let c_t run over the full orbit.  Precisely:
     every S4-image pair (a,b) is conjugate under the centralizer of a to one of
       OCT(e) : b = [[p,1],[-1/4,s]], p=(1+e r2)/2, s=(1-e r2)/2, r2 = sqrt(-2)  (S4 faithful)
       S3     : b = [[1/2,1],[-3/4,1/2]]                            (S4 -> S3)
       TRIV   : b = I                                                (S4 -> Z2)
     (b of order 3 with (ab)^4 = 1: tr(b)^2 = det b, tr(ab)^2 in {2 det b, 0};
     scale tr b = 1; the entries q, r of b are both nonzero -- q = 0 would force
     ps = 1, but ps = (1 + 2)/4 = 3/4 (OCT) or 1/4 (S3), since tr(ab) = p - s -- and diag(t,1) rescales q
     to 1.)  Then c runs over the full orbit {c_t : t in C^*} union {a}.
For each S and each b-class, the relators give polynomials in t over Q(sqrt 2):
M12 = 0, M21 = 0, M11 - M22 = 0.  Their gcd, with factors t removed, is the
exact solution set.  Here r2 denotes sqrt(-2) and K = Q(sqrt(-2)).  Constant gcd => no representation.
"""
import sys, itertools
import sympy as sp
sys.path.insert(0, 'experiments/thompson-v-models')
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
from census import load, word_str  # noqa: E402

t = sp.symbols('t')
r2 = sp.sqrt(-2)   # det a = -1, so tr(ab)^2 = 2 det(ab) = -2 det b
K = sp.QQ.algebraic_field(r2)

a = sp.Matrix([[1, 0], [0, -1]])
bclasses = {}
for e in (1, -1):
    p = (1 + e * r2) / 2; s = (1 - e * r2) / 2
    bclasses['OCT%+d' % e] = sp.Matrix([[p, 1], [-sp.Rational(1, 4), s]])
bclasses['S3'] = sp.Matrix([[sp.Rational(1, 2), 1], [-sp.Rational(3, 4), sp.Rational(1, 2)]])
bclasses['TRIV'] = sp.eye(2)


def adj(M):  # inverse up to scalar
    return sp.Matrix([[M[1, 1], -M[0, 1]], [-M[1, 0], M[0, 0]]])


def is_scalar(M):
    M = M.applyfunc(sp.simplify)
    return M[0, 1] == 0 and M[1, 0] == 0 and sp.simplify(M[0, 0] - M[1, 1]) == 0


def check_S4(b):
    ab = a * b
    return is_scalar(b ** 3) and is_scalar(ab ** 4)


def word_matrix(w, gens):
    M = sp.eye(2)
    for ch in w:
        M = (M * gens[ch]).applyfunc(sp.expand)
    return M


def main(relfile):
    Rw = [word_str(w) for w in load(relfile)]
    names = ['r%d' % (i + 5) for i in range(len(Rw))]
    ct = sp.Matrix([[t, t ** 2], [3, -t]])
    assert is_scalar(ct * ct) and is_scalar((a * ct) ** 3)
    results = {}
    for bn, b in bclasses.items():
        assert check_S4(b), bn
        gens = {'a': a, 'b': b, 'B': adj(b), 'c': ct}
        gens_deg = {'a': a, 'b': b, 'B': adj(b), 'c': a}   # c = a
        polys, degok = [], []
        for w in Rw:
            M = word_matrix(w, gens)
            polys.append([sp.Poly(M[0, 1], t, domain=K), sp.Poly(M[1, 0], t, domain=K),
                          sp.Poly(M[0, 0] - M[1, 1], t, domain=K)])
            degok.append(is_scalar(word_matrix(w, gens_deg)))
        for r in range(1, len(Rw) + 1):
            for S in itertools.combinations(range(len(Rw)), r):
                g = sp.Poly(0, t, domain=K)
                for i in S:
                    for q in polys[i]:
                        g = sp.gcd(g, q)
                while not g.is_zero and g.degree() > 0 and g.eval(0) == 0:
                    g = sp.Poly(sp.quo(g.as_expr(), t), t, domain=K)
                lab = '{' + ','.join(names[i] for i in S) + '}'
                results[(bn, lab)] = (g, all(degok[i] for i in S))
        print(bn, 'relator degrees in t:', [max(q.degree() for q in P) for P in polys], flush=True)
    for (bn, lab), (g, dg) in results.items():
        desc = 'identically zero' if g.is_zero else ('deg %d: %s' % (g.degree(), g.as_expr()) if g.degree() > 0 else 'none')
        print(f'{bn:6s} {lab:16s} c_t-solutions: {desc}; c=a solution: {dg}')


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'experiments/thompson-v-models/rel_V.txt')
