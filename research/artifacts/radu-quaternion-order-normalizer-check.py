# Exact: conjugation by each rho(s), s in {a,b,c,x,y,z}, maps the order O = O_F[1/2]<1,g,h,gh>
# into itself (coefficients in Z[1/2][w]); and every relator-free generator image normalizes B.
from fractions import Fraction as Fr
exec(open("radu-quaternion-invariants-check.py").read().split('print("DONE")')[0])

def Finv(p):
    n = Fnorm(p)
    conj = (p[0] + p[1] * Fr(1, 2), -p[1])  # conjugate of a + b w is a + b w' with w' = 1/2 - w
    return (conj[0] / n, conj[1] / n)

def Fsolve(Mx, rhs):
    n = len(Mx)
    A = [row[:] + [rhs[i]] for i, row in enumerate(Mx)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != (Fr(0), Fr(0)))
        A[col], A[piv] = A[piv], A[col]
        ip = Finv(A[col][col])
        A[col] = [Fmul(ip, v) for v in A[col]]
        for r in range(n):
            if r != col and A[r][col] != (Fr(0), Fr(0)):
                fct = A[r][col]
                A[r] = [Fadd(A[r][k], Fneg(Fmul(fct, A[col][k]))) for k in range(n + 1)]
    return [A[i][n] for i in range(n)]

def Fto_R(p):
    # alpha + beta w in the m-basis, w = 1/2 + m^2/2 - m^3
    return norm({(0, 0): p[0] + p[1] * Fr(1, 2), (2, 0): p[1] * Fr(1, 2), (3, 0): -p[1]})

def adj(A):
    return [[A[1][1], neg(A[0][1])], [neg(A[1][0]), A[0][0]]]

def is_dyadic(q):
    d = q.denominator
    while d % 2 == 0:
        d //= 2
    return d == 1

ok = True
gens6 = {"a": a, "b": b, "c": c, "x": x, "y": y, "z": z}
mp1sq_inv = mul(inv_m1, inv_m1)
detinv = {
    "a": neg(inv_m), "b": neg(inv_m), "x": const(-1), "z": const(-1),
    "y": mul(const(Fr(1, 4)), mp1sq_inv),
    "c": neg(mul(const(Fr(1, 16)), mul(inv_m, mul(mp1sq_inv, mp1sq_inv)))),
}
for sname, S in gens6.items():
    Sadj = adj(S)
    detS = add(mul(S[0][0], S[1][1]), neg(mul(S[0][1], S[1][0])))
    assert mul(detS, detinv[sname]) == const(1), sname
    for ename, E in (("1", basis[0]), ("g", g), ("h", h), ("gh", gh)):
        C = mmul(mmul(S, E), Sadj)  # = det(S) * S E S^{-1}
        target = [[mul(detinv[sname], C[i][j]) for j in range(2)] for i in range(2)]  # S E S^{-1}
        rhs = [in_F(tr(mmul(target, basis[j]))) for j in range(4)]
        if any(v is None for v in rhs):
            print("s =", sname, "e =", ename, ": traces not in F")
            ok = False
            continue
        coeffs = Fsolve(T, rhs)
        recon = [[{}, {}], [{}, {}]]
        for cf, Bm in zip(coeffs, basis):
            recon = [[add(recon[i][j], mul(Fto_R(cf), Bm[i][j])) for j in range(2)] for i in range(2)]
        exact = all(add(recon[i][j], neg(target[i][j])) == {} for i in range(2) for j in range(2))
        dyadic = all(is_dyadic(v) for cf in coeffs for v in cf)
        print("s=%s e=%-2s in B: %s  coefficients in Z[1/2][w]: %s  %s" % (sname, ename, exact, dyadic, coeffs))
        ok = ok and exact and dyadic
print("ALL CONJUGATES IN O:", ok)
print("DONE2")
