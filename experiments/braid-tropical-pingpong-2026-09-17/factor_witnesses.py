# Exact factorization of the characteristic polynomials of LK_4(a) and LK_4([a,b]) over Z[q^±1, t^±1],
# with a = s1 s3^-1, b = s2 a s2^-1 (generators of the point-push F_2 = ker(B_4 -> B_3)).
# These factorizations hold identically, so they survive every specialization (q0, t0) in K^* x K^*.
import sympy as sp
from lk import sigma, q, t
x = sp.Symbol('x')
S = {i: sigma(i, 4) for i in (1, 2, 3)}
Si = {i: S[i].inv() for i in (1, 2, 3)}
a = (S[1] * Si[3]).applyfunc(sp.cancel)
b = (S[2] * a * Si[2]).applyfunc(sp.cancel)
A = a.inv().applyfunc(sp.cancel)
B = b.inv().applyfunc(sp.cancel)
z = (a * b * A * B).applyfunc(sp.cancel)
for name, M in (('a', a), ('[a,b]=abAB', z)):
    cp = sp.factor(sp.cancel(M.charpoly(x).as_expr()))
    print(name, ':', cp)
# Delta conjugates s1 to s3, hence a to a^-1; check the spectrum symmetry directly:
D = S[1] * S[2] * S[3] * S[1] * S[2] * S[1]
print('Delta a Delta^-1 == a^-1:', (D * a - A * D).applyfunc(sp.cancel) == sp.zeros(6, 6))
# Full twists: Delta_4^2 is a scalar; compare [a,b] with Delta_4^2 Delta_3^-2.
D3 = S[1] * S[2] * S[1]
D4sq = (D * D).applyfunc(sp.cancel)
print('Delta_4^2 is scalar:', D4sq == D4sq[0, 0] * sp.eye(6), sp.factor(D4sq[0, 0]))
Z = (D4sq * (D3 * D3).inv()).applyfunc(sp.cancel)
print('charpoly Delta_4^2 Delta_3^-2:', sp.factor(sp.cancel(Z.charpoly(x).as_expr())))
