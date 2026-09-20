# Checks for research/mod-s2-bielliptic-centralizer-has-rational-h2.md
# Pure integer arithmetic; run: python3 check.py
from fractions import Fraction
from itertools import product


def mul(X, Y):
    n, m, p = len(X), len(Y), len(Y[0])
    return [[sum(X[i][k] * Y[k][j] for k in range(m)) for j in range(p)] for i in range(n)]


def tr(X):
    return [list(r) for r in zip(*X)]


def inv2(X):
    a, b = X[0]
    c, d = X[1]
    assert a * d - b * c == 1
    return [[d, -b], [-c, a]]


I2 = [[1, 0], [0, 1]]
MI2 = [[-1, 0], [0, -1]]
A = [[1, 2], [0, 1]]
B = [[1, 0], [2, 1]]
GENS = {'A': A, 'a': inv2(A), 'B': B, 'b': inv2(B)}


def size(X):
    return sum(abs(v) for r in X for v in r)


def ab_coords(M):
    """Abelianization of Gamma(2)/{+-I} = F(A,B), by greedy Sanov reduction."""
    M = [row[:] for row in M]
    x = y = 0
    steps = 0
    while not (M == I2 or M == MI2):
        best = None
        for k, G in GENS.items():
            N = mul(G, M)
            if best is None or size(N) < best[0]:
                best = (size(N), k, N)
        assert best[0] < size(M), "reduction stuck: not in Gamma(2)?"
        k, M = best[1], best[2]
        # new M = G * old M, so old M = G^{-1} * new M; record G^{-1}
        x += {'A': -1, 'a': 1, 'B': 0, 'b': 0}[k]
        y += {'A': 0, 'a': 0, 'B': -1, 'b': 1}[k]
        steps += 1
        assert steps < 10000
    return (x, y)


assert ab_coords(A) == (1, 0) and ab_coords(B) == (0, 1)
assert ab_coords(mul(mul(A, B), mul(inv2(A), B))) == (0, 2)

S = [[0, -1], [1, 0]]
T = [[1, 1], [0, 1]]


def conj_action(G):
    cols = [ab_coords(mul(mul(G, X), inv2(G))) for X in (A, B)]
    return [[cols[0][0], cols[1][0]], [cols[0][1], cols[1][1]]]  # columns: images of [A],[B]


RS, RT = conj_action(S), conj_action(T)
print("S acts on H1(Gamma(2);Z) by", RS, "; T acts by", RT)

# S3-invariant bilinear forms b: R^T b R = b for R in {RS, RT}
sols = []
for vals in product(range(-3, 4), repeat=4):
    Bm = [list(vals[:2]), list(vals[2:])]
    if any(vals) and all(mul(mul(tr(R), Bm), R) == Bm for R in (RS, RT)):
        sols.append(Bm)
print("nonzero invariant bilinear forms, entries in [-3,3]:", sols)
base = sols[0]
for s in sols:  # all proportional: coinvariants of H1 (x) H1 are one-dimensional
    lam = Fraction(s[0][0], base[0][0])
    assert all(s[i][j] == lam * base[i][j] for i in range(2) for j in range(2))
print("b([A],[B]) =", base[0][1], "; b([A],[A]) =", base[0][0])
assert base[0][1] != 0

# ---- symplectic side: basis a1, b1, a2, b2 with <a_i, b_i> = 1 ----
Om = [[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]]


def form(x, y):
    return sum(x[i] * Om[i][j] * y[j] for i in range(4) for j in range(4))


def transvection(v):
    # x -> x + <x, v> v, as a matrix acting on column vectors
    w = [sum(Om[j][k] * v[k] for k in range(4)) for j in range(4)]  # <x,v> = w . x
    return [[(1 if i == j else 0) + v[i] * w[j] for j in range(4)] for i in range(4)]


def col(X, q):
    return [X[i][q] for i in range(4)]


def is_symp(X):
    return all(form(col(X, p), col(X, q)) == Om[p][q] for p in range(4) for q in range(4))


def apply(X, v):
    return [sum(X[i][j] * v[j] for j in range(4)) for i in range(4)]


J = [[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]  # a1 <-> a2, b1 <-> b2
assert is_symp(J)
c = [1, 0, 1, 0]    # [c]  = a1 + a2
cp = [0, 1, 0, -1]  # [c'] = b1 - b2
Tc, Tcp = transvection(c), transvection(cp)
for X in (Tc, Tcp):
    assert is_symp(X) and mul(X, J) == mul(J, X)
assert mul(Tc, Tcp) == mul(Tcp, Tc) and form(c, cp) == 0
e, f, ep, fp = [1, 0, 1, 0], [0, 1, 0, 1], [1, 0, -1, 0], [0, 1, 0, -1]


def restrict(X, basis):
    u0, u1 = basis
    out = []
    for v in basis:
        w = apply(X, v)
        sol = None
        for (p, q) in [(0, 1), (0, 3), (2, 1), (2, 3)]:
            det = u0[p] * u1[q] - u0[q] * u1[p]
            if det:
                al = Fraction(w[p] * u1[q] - w[q] * u1[p], det)
                be = Fraction(u0[p] * w[q] - u0[q] * w[p], det)
                sol = (al, be)
                break
        al, be = sol
        assert [al * u0[i] + be * u1[i] for i in range(4)] == w, "subspace not preserved"
        out.append((int(al), int(be)))
    return [[out[0][0], out[1][0]], [out[0][1], out[1][1]]]


for name, X in (("T_c ", Tc), ("T_c'", Tcp)):
    print(name, "on L+ (e,f):", restrict(X, (e, f)), "; on L- (e',f'):", restrict(X, (ep, fp)))
print("<e,f> =", form(e, f), "; <e',f'> =", form(ep, fp))

# Image of the torus: (x_A^{s1}) (x) (x_B^{s2}) paired with b
X1 = restrict(Tc, (e, f))
Y2 = restrict(Tcp, (ep, fp))
s1 = ab_coords(X1)   # coordinates of [first-factor image] in H1(Gamma(2))
s2 = ab_coords(Y2)
val = sum(s1[i] * base[i][j] * s2[j] for i in range(2) for j in range(2))
print("abelianized torus generators:", s1, s2, "; b-pairing of the torus class =", val)
assert val != 0
print("ALL CHECKS PASSED")
