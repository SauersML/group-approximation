# Independent exact check of quaternionic representations rho : Gamma_c -> D^*/K^* over K = F_2(t),
# D = [a, b) (i^2 = i + a, j^2 = b, j i = (i + 1) j), for the classes in REPS below.  Generalises
# experiments/bmw-klein-free-2026-09-18/verify_quat_rep.py to arbitrary (a, b, PV, PH); it uses sympy
# polynomials over GF(2) and a structure-constant table, none of quat.py / gf2poly.py.  Per entry:
#   (1) the structure constants are associative;
#   (2) Gram determinant det Trd(e_r e_s) = b^2, so O = F_2[t]<1,i,j,k> has reduced discriminant b;
#   (3) x^2 + x + a has no root mod b (b irreducible here), so D is ramified at b (a division algebra);
#   (4) every defining relation of Gamma_c holds in D^*/K^*: x x' scalar for inverse letters (x^2 scalar
#       for involutions) and h v = scalar * v' h' for all m n squares;
#   (5) at PH every h-letter is primitive with val(Nrd) = 1 and every v-letter has val 0, at PV the
#       reverse, and distinct h-letters (v-letters) move the base vertex at PH (PV) to distinct neighbours.
# Coordinates are ints (bit i = coefficient of t^i) in the basis (c0 + c1 i) + (c2 + c3 i) j = c0 + c1 i + c2 j + c3 k.
import json, itertools
from sympy import Poly, symbols, Matrix
T = symbols('t')
def P(c): return Poly(c, T, modulus=2)
ZERO, ONE = P(0), P(1)
def dec(c): return P(sum(T ** e for e in range(c.bit_length()) if c >> e & 1))
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
# (census, class): (a, b, PV, PH, H letters, V letters)   [a, b, PV, PH as ints]
REPS = {
  ('census_30_30.json', 16): (2, 7, 2, 3, {0: (7, 0, 2, 0), 1: (7, 0, 2, 1), 2: (7, 0, 3, 1)},
                                          {0: (7, 0, 3, 0), 1: (0, 0, 0, 1), 2: (0, 0, 1, 1)}),
  ('census_50_31.json', 243): (1, 3, 2, 7, {0: (3, 0, 0, 2), 1: (0, 0, 1, 2), 2: (0, 0, 1, 3), 3: (2, 0, 1, 1), 4: (2, 0, 1, 0)},
                                           {0: (0, 1, 0, 1), 1: (1, 1, 0, 1), 2: (3, 0, 0, 1)}),
  ('census_51_30.json', 660): (1, 3, 2, 7, {0: (0, 3, 0, 2), 1: (3, 3, 0, 2), 2: (0, 0, 3, 2), 3: (0, 0, 3, 1), 4: (3, 0, 0, 2)},
                                           {0: (1, 0, 1, 0), 1: (1, 0, 1, 1), 2: (1, 0, 0, 1)}),
  ('census_51_31.json', 279): (1, 3, 2, 7, {0: (0, 3, 0, 2), 1: (3, 3, 0, 2), 2: (0, 0, 1, 3), 3: (0, 0, 1, 2), 4: (3, 0, 0, 2)},
                                           {0: (1, 1, 0, 1), 1: (0, 1, 0, 1), 2: (1, 0, 0, 1)}),
  ('census_51_31.json', 309): (1, 3, 2, 7, {0: (1, 3, 0, 0), 1: (2, 3, 0, 0), 2: (2, 0, 0, 1), 3: (2, 0, 1, 0), 4: (2, 0, 1, 1)},
                                           {0: (0, 3, 0, 1), 1: (3, 3, 0, 1), 2: (3, 0, 0, 1)}),
  ('census_52_30.json', 386): (1, 3, 2, 7, {0: (0, 3, 0, 2), 1: (3, 3, 0, 2), 2: (2, 3, 0, 0), 3: (1, 3, 0, 0), 4: (2, 0, 0, 1)},
                                           {0: (1, 0, 1, 0), 1: (1, 0, 1, 1), 2: (3, 0, 0, 1)}),
  ('census_52_31.json', 185): (1, 3, 2, 7, {0: (0, 3, 0, 2), 1: (3, 3, 0, 2), 2: (3, 1, 0, 0), 3: (2, 1, 0, 0), 4: (2, 0, 0, 1)},
                                           {0: (1, 1, 0, 1), 1: (0, 1, 0, 1), 2: (3, 0, 0, 1)}),
}
def check_algebra(a, b):
    M = [[None] * 4 for _ in range(4)]
    def vec(*c): return [x if isinstance(x, Poly) else P(x) for x in c]
    for s in range(4):
        M[0][s] = [ONE if u == s else ZERO for u in range(4)]; M[s][0] = list(M[0][s])
    M[1][1] = vec(a, 1, 0, 0); M[1][2] = vec(0, 0, 0, 1); M[1][3] = vec(0, 0, a, 1)
    M[2][1] = vec(0, 0, 1, 1); M[2][2] = vec(b, 0, 0, 0); M[2][3] = vec(b, b, 0, 0)
    M[3][1] = vec(0, 0, a, 0); M[3][2] = vec(0, b, 0, 0); M[3][3] = vec(a * b, 0, 0, 0)
    def mul(X, Y):
        Z = [ZERO] * 4
        for r in range(4):
            for s in range(4):
                if X[r].is_zero or Y[s].is_zero: continue
                c = X[r] * Y[s]
                for u in range(4): Z[u] = Z[u] + c * M[r][s][u]
        return Z
    E = [[ONE if u == r else ZERO for u in range(4)] for r in range(4)]
    for r, s, u in itertools.product(range(4), repeat=3):                           # (1)
        assert mul(mul(E[r], E[s]), E[u]) == mul(E[r], mul(E[s], E[u])), (r, s, u)
    assert mul(E[2], E[1]) == mul(vec(1, 1, 0, 0), E[2])
    trd = lambda X: X[1]
    Gm = Matrix(4, 4, lambda r, s: trd(mul(E[r], E[s])).as_expr())                 # (2)
    assert Poly(Gm.det(), T, modulus=2) == b * b
    assert b.is_irreducible                                                           # (3)
    db = b.degree()
    for cs in itertools.product((0, 1), repeat=db):
        x = P(sum(c * T ** e for e, c in enumerate(cs)))
        assert not (x ** 2 + x + a).rem(b).is_zero
    return mul
for (f, ci), (ai, bi, pv, ph, Hc, Vc) in REPS.items():
    a, b, PV, PH = dec(ai), dec(bi), dec(pv), dec(ph)
    mul = check_algebra(a, b)
    conj = lambda X: [X[0] + X[1], X[1], X[2], X[3]]
    def nrd(X):
        Z = mul(X, conj(X)); assert Z[1].is_zero and Z[2].is_zero and Z[3].is_zero; return Z[0]
    def val(p, pl):
        v = 0
        while p.rem(pl).is_zero: p = p.quo(pl); v += 1
        return v
    def dist(X, pl): return val(nrd(X), pl) - 2 * min(val(x, pl) for x in X if not x.is_zero)
    scalar = lambda X: X[1].is_zero and X[2].is_zero and X[3].is_zero and not X[0].is_zero
    propeq = lambda X, Y: all((X[u] * Y[w] - X[w] * Y[u]).is_zero for u in range(4) for w in range(4)) and any(not x.is_zero for x in X)
    assert not b.rem(PV).is_zero and not b.rem(PH).is_zero and PV.is_irreducible and PH.is_irreducible
    D = json.load(open(C + f)); iA, iB = D['iA'], D['iB']
    SQ = [(tuple(x), tuple(y)) for x, y in D['reps'][ci]]
    H = {x: [dec(c) for c in Hc[x]] for x in Hc}; V = {x: [dec(c) for c in Vc[x]] for x in Vc}
    assert len(H) == len(iA) and len(V) == len(iB) and len(SQ) == len(iA) * len(iB)
    for L, inv in ((H, iA), (V, iB)):
        for x in L: assert scalar(mul(L[x], L[inv[x]])), (f, x)                      # (4)
    for (h, v), (v2, h2) in SQ: assert propeq(mul(H[h], V[v]), mul(V[v2], H[h2])), (f, h, v)
    for L, near, far in ((H, PH, PV), (V, PV, PH)):                                  # (5)
        for x in L:
            assert min(val(c, near) for c in L[x] if not c.is_zero) == 0
            assert min(val(c, far) for c in L[x] if not c.is_zero) == 0
            assert dist(L[x], near) == 1 and dist(L[x], far) == 0
        for x, y in itertools.combinations(L, 2):
            assert dist(mul(conj(L[x]), L[y]), near) != 0, (f, x, y)
    print(f, ci, 'OK: D = [%s, %s), PV = %s, PH = %s;' % (a.as_expr(), b.as_expr(), PV.as_expr(), PH.as_expr()),
          'rho is a homomorphism satisfying the tree conditions', flush=True)
print('all', len(REPS), 'representations OK')
