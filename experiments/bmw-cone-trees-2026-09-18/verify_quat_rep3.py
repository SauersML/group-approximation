# Independent exact check of the characteristic-3 quaternionic representations rho : Gamma_c -> D^*/K^*,
# K = F_3(t), D = (a, b) (i^2 = a, j^2 = b, k = ij = -ji), for every record with found = true in the
# search logs quat3_44.jsonl and quat3b_44.jsonl (written by findquat3.py).  Uses sympy polynomials
# over GF(3) and a structure-constant table, none of quatp.py / fpoly.py.  Per entry:
#   (1) the structure constants are associative;
#   (2) det Trd(e_r e_s) = unit * b^2, so O = F_3[t]<1,i,j,k> has reduced discriminant b (a is a unit);
#   (3) a is not a square mod b (b irreducible), so D is ramified at b (a division algebra);
#   (4) every defining relation holds in D^*/K^*: x x' scalar for inverse letters, h v = scalar * v' h';
#   (5) at PH every h-letter has content prime to PH, val(Nrd) = 1, and every v-letter has d = 0; at PV
#       the reverse; distinct h-letters (v-letters) move the base vertex at PH (PV) to distinct neighbours.
# Coordinates: lists of coefficients (lowest degree first) of x0 + x1 i + x2 j + x3 k.
import json, itertools
from sympy import Poly, symbols, Matrix
T = symbols('t'); p = 3
def P(c): return Poly(c, T, modulus=p)
def dec(cs): return P(sum(int(c) * T ** e for e, c in enumerate(cs)))
ZERO, ONE = P(0), P(1)
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
LOGS = ['quat3_44.jsonl', 'quat3b_44.jsonl']
def algebra(a, b):
    M = [[None] * 4 for _ in range(4)]
    vec = lambda *c: [x if isinstance(x, Poly) else P(x) for x in c]
    for s in range(4):
        M[0][s] = [ONE if u == s else ZERO for u in range(4)]; M[s][0] = list(M[0][s])
    M[1][1] = vec(a, 0, 0, 0); M[1][2] = vec(0, 0, 0, 1); M[1][3] = vec(0, 0, a, 0)
    M[2][1] = vec(0, 0, 0, -1); M[2][2] = vec(b, 0, 0, 0); M[2][3] = vec(0, -b, 0, 0)
    M[3][1] = vec(0, 0, -a, 0); M[3][2] = vec(0, b, 0, 0); M[3][3] = vec(-a * b, 0, 0, 0)
    def mul(X, Y):
        Z = [ZERO] * 4
        for r in range(4):
            for s in range(4):
                if X[r].is_zero or Y[s].is_zero: continue
                c = X[r] * Y[s]
                for u in range(4): Z[u] = Z[u] + c * M[r][s][u]
        return Z
    E = [[ONE if u == r else ZERO for u in range(4)] for r in range(4)]
    for r, s, u in itertools.product(range(4), repeat=3):                             # (1)
        assert mul(mul(E[r], E[s]), E[u]) == mul(E[r], mul(E[s], E[u])), (r, s, u)
    assert mul(E[1], E[2]) == E[3] and mul(E[2], E[1]) == [-x for x in E[3]]
    trd = lambda X: 2 * X[0]
    G = Poly(Matrix(4, 4, lambda r, s: trd(mul(E[r], E[s])).as_expr()).det(), T, modulus=p)
    q, r = G.div(b * b); assert r.is_zero and q.degree() == 0 and not q.is_zero        # (2)
    assert a.degree() == 0 and b.is_irreducible                                        # (3)
    for cs in itertools.product(range(p), repeat=b.degree()):
        x = P(sum(c * T ** e for e, c in enumerate(cs)))
        assert not (x ** 2 - a).rem(b).is_zero
    return mul
recs = {}
for LOG in LOGS:
    for l in open(LOG):
        if l.startswith('{'):
            r = json.loads(l)
            if r['found']: recs.setdefault((r['census'], r['cls']), r)
REPS = sorted(recs)
for f, ci in REPS:
    r = recs[f, ci]
    a, b, PV, PH = dec(r['a']), dec(r['b']), dec(r['PV']), dec(r['PH'])
    mul = algebra(a, b)
    conj = lambda X: [X[0], -X[1], -X[2], -X[3]]
    def nrd(X):
        Z = mul(X, conj(X)); assert Z[1].is_zero and Z[2].is_zero and Z[3].is_zero; return Z[0]
    def val(q, pl):
        v = 0
        while q.rem(pl).is_zero: q = q.quo(pl); v += 1
        return v
    def dist(X, pl): return val(nrd(X), pl) - 2 * min(val(x, pl) for x in X if not x.is_zero)
    scalar = lambda X: X[1].is_zero and X[2].is_zero and X[3].is_zero and not X[0].is_zero
    propeq = lambda X, Y: all((X[u] * Y[w] - X[w] * Y[u]).is_zero for u in range(4) for w in range(4)) and any(not x.is_zero for x in X)
    assert PV.is_irreducible and PH.is_irreducible and PV != PH
    assert not b.rem(PV).is_zero and not b.rem(PH).is_zero
    D = json.load(open(C + f)); iA, iB = D['iA'], D['iB']
    SQ = [(tuple(x), tuple(y)) for x, y in D['reps'][ci]]
    H = {int(x): [dec(c) for c in v] for x, v in r['H'].items()}
    V = {int(x): [dec(c) for c in v] for x, v in r['V'].items()}
    assert sorted(H) == list(range(len(iA))) and sorted(V) == list(range(len(iB)))
    assert len(SQ) == len(iA) * len(iB)
    for L, inv in ((H, iA), (V, iB)):
        for x in L: assert scalar(mul(L[x], L[inv[x]])), (f, x)                        # (4)
    for (h, v), (v2, h2) in SQ: assert propeq(mul(H[h], V[v]), mul(V[v2], H[h2])), (f, h, v)
    for L, near, far in ((H, PH, PV), (V, PV, PH)):                                    # (5)
        for x in L:
            assert min(val(c, near) for c in L[x] if not c.is_zero) == 0
            assert min(val(c, far) for c in L[x] if not c.is_zero) == 0
            assert dist(L[x], near) == 1 and dist(L[x], far) == 0
        for x, y in itertools.combinations(L, 2):
            assert dist(mul(conj(L[x]), L[y]), near) != 0, (f, x, y)
    show = lambda X: ', '.join(str(c.as_expr()) for c in X)
    print(f, ci, 'OK: D = (%s, %s) over F_3(t), PV = %s, PH = %s;' % (a.as_expr(), b.as_expr(), PV.as_expr(), PH.as_expr()),
          'rho is a homomorphism satisfying the tree conditions', flush=True)
    for L, nm in ((H, 'h'), (V, 'v')):
        for x in sorted(L): print('   %s_%d = (%s)   Nrd = %s' % (nm, x, show(L[x]), nrd(L[x]).as_expr()))
print('all', len(REPS), 'representations OK')
