# Independent exact check of the quaternionic representations rho : Gamma_c -> D^*/K^* for
# 31_30 #26 and 31_31 #12.  It uses sympy polynomials over GF(2) and a structure-constant table for
# D = [t, t^2+t+1) in the basis 1, i, j, k = ij (i^2 = i + a, j^2 = b, j i = (i + 1) j), derived below,
# and none of quat.py / gf2poly.py.  It checks:
#   (1) the structure constants are associative (so D is a quaternion algebra with this table);
#   (2) Gram determinant det Trd(e_r e_s) = b^2, so O = F_2[t]<1,i,j,k> has reduced discriminant b and
#       is maximal at every prime not dividing b, in particular at t and t+1;
#   (3) the Artin-Schreier polynomial x^2 + x + a has no root mod b (= residue field F_4), so D is
#       ramified at b (hence a division algebra);
#   (4) every defining relation of Gamma_c holds in D^*/K^*: x x' = scalar for inverse letters,
#       x^2 = scalar for involutions, h v = scalar * v' h' for all 9 squares;
#   (5) at PH = t+1 every h-letter is primitive with val(Nrd) = 1 and every v-letter has val 0;
#       at PV = t the reverse; and for x != y the quotient x^{-1} y of two h-letters (resp. v-letters)
#       has distance != 0 at PH (resp. PV), i.e. the letters move the base vertex to distinct neighbours.
import json, itertools
from sympy import Poly, symbols, GF
T = symbols('t')
def P(c): return Poly(c, T, modulus=2)
ZERO, ONE = P(0), P(1)
a, b = P(T), P(T**2 + T + 1)
# basis e0=1, e1=i, e2=j, e3=k=ij.  Table M[r][s] = coordinates of e_r e_s.
#   i i = a + i;  i j = k;  i k = a j + k;  j i = j + k;  j j = b;  j k = b + b i;
#   k i = a j;  k j = b i;  k k = a b.
M = [[None] * 4 for _ in range(4)]
def vec(*c): return [P(x) if not isinstance(x, Poly) else x for x in c]
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
# (1) associativity on basis
for r, s, u in itertools.product(range(4), repeat=3):
    assert mul(mul(E[r], E[s]), E[u]) == mul(E[r], mul(E[s], E[u])), (r, s, u)
# the defining relations i^2 = i + a, j^2 = b, j i = (1 + i) j hold by the table
assert mul(E[1], E[1]) == vec(a, 1, 0, 0) and mul(E[2], E[2]) == vec(b, 0, 0, 0)
assert mul(E[2], E[1]) == mul(vec(1, 1, 0, 0), E[2])
# reduced trace and norm: conj(x) = Trd(x) - x, with Trd(e0)=0 (char 2: Trd(1) = 2 = 0), Trd(i)=1, Trd(j)=Trd(k)=0
def trd(X): return X[1]
def conj(X): return [X[0] + X[1], X[1], X[2], X[3]]
def nrd(X):
    Z = mul(X, conj(X)); assert Z[1].is_zero and Z[2].is_zero and Z[3].is_zero; return Z[0]
for X in E: assert mul(conj(X), X) == mul(X, conj(X))
# (2) Gram determinant of the reduced trace form on O
from sympy import Matrix
Gm = Matrix(4, 4, lambda r, s: trd(mul(E[r], E[s])).as_expr())
det = Poly(Gm.det(), T, modulus=2)
assert det == b * b, det
# (3) x^2 + x + a has no root in F_2[t]/(b) = F_4: test the 4 residues c0 + c1 t
roots = [(c0, c1) for c0 in (0, 1) for c1 in (0, 1) if (P(c0 + c1 * T) ** 2 + P(c0 + c1 * T) + a).rem(b).is_zero]
assert roots == [], roots
def val(p, pl):
    v = 0
    while p.rem(pl).is_zero: p = p.quo(pl); v += 1
    return v
PT, PT1 = P(T), P(T + 1)
def dist(X, pl): return val(nrd(X), pl) - 2 * min(val(x, pl) for x in X if not x.is_zero)
def scalar(X): return X[1].is_zero and X[2].is_zero and X[3].is_zero and not X[0].is_zero
def propeq(X, Y):          # X = lambda Y with lambda in K^*
    return all((X[u] * Y[w] - X[w] * Y[u]).is_zero for u in range(4) for w in range(4)) and any(not x.is_zero for x in X)
def dec(c):                # int -> polynomial over F_2 (bit i = coefficient of t^i)
    return P(sum(T ** e for e in range(c.bit_length()) if c >> e & 1))
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
REPS = {
  ('census_31_30.json', 26): ({0: (2, 1, 1, 0), 1: (3, 1, 1, 0), 2: (2, 0, 1, 0)},
                              {0: (0, 0, 0, 1), 1: (7, 0, 3, 0), 2: (0, 0, 1, 1)}),
  ('census_31_31.json', 12): ({0: (2, 1, 1, 0), 1: (3, 1, 1, 0), 2: (2, 0, 1, 0)},
                              {0: (1, 1, 0, 0), 1: (0, 1, 0, 0), 2: (3, 0, 1, 0)}),
}
for (f, ci), (Hc, Vc) in REPS.items():
    D = json.load(open(C + f)); iA, iB = D['iA'], D['iB']
    SQ = [(tuple(x), tuple(y)) for x, y in D['reps'][ci]]
    H = {x: [dec(c) for c in Hc[x]] for x in Hc}; V = {x: [dec(c) for c in Vc[x]] for x in Vc}
    assert len(H) == len(iA) == 3 and len(V) == len(iB) == 3 and len(SQ) == 9
    for L, inv in ((H, iA), (V, iB)):
        for x in L: assert scalar(mul(L[x], L[inv[x]])), (f, x)          # (4) inverse / involution
    for (h, v), (v2, h2) in SQ: assert propeq(mul(H[h], V[v]), mul(V[v2], H[h2])), (f, h, v)
    for L, near, far in ((H, PT1, PT), (V, PT, PT1)):                    # (5)
        for x in L:
            assert min(val(c, near) for c in L[x] if not c.is_zero) == 0
            assert min(val(c, far) for c in L[x] if not c.is_zero) == 0
            assert dist(L[x], near) == 1 and dist(L[x], far) == 0
        for x, y in itertools.combinations(L, 2):
            assert dist(mul(conj(L[x]), L[y]), near) != 0, (f, x, y)
    print(f, ci, 'OK: rho is a homomorphism satisfying the tree conditions at t and t+1;',
          'Nrd(h) =', [str(nrd(H[x]).as_expr()) for x in H], 'Nrd(v) =', [str(nrd(V[x]).as_expr()) for x in V])
print('D = [t, t^2+t+1): associative table, disc(O) = b, ramified at b: all OK')
