# Action of the horizontal quotient Q of Radu's lattice on the Bruhat-Tits tree T' at the second prime
# q' above 2 (w = m + 1/m with v_2(w) = +1). Exact over F, then 2-adic at q'.
# Checks: <xz, xyx> (an S_3) fixes a vertex p of T', is transitive on its three edges, and some
# element of rho(V) inverts an edge at p  ==>  rho(V) is vertex-transitive on T'.
from fractions import Fraction as Fr
src = open("radu-quaternion-order-normalizer-check.py").read().split('ok = True')[0]
exec(src)
ZERO = (Fr(0), Fr(0)); ONE = (Fr(1), Fr(0))
E = basis
def coeffs_of(Mx):
    rhs = [in_F(tr(mmul(Mx, E[j]))) for j in range(4)]
    return Fsolve(T, rhs)
# structure constants c[i][j] = coefficients of e_i e_j
c = [[coeffs_of(mmul(E[i], E[j])) for j in range(4)] for i in range(4)]
inv_m1sq = mul(inv_m1, inv_m1)
detinv = {"a": neg(inv_m), "b": neg(inv_m), "x": const(-1), "z": const(-1),
          "y": mul(const(Fr(1, 4)), inv_m1sq),
          "c": neg(mul(const(Fr(1, 16)), mul(inv_m, mul(inv_m1sq, inv_m1sq))))}
L6 = {"a": a, "b": b, "c": c_ if False else None}
L6 = {"a": a, "b": b, "x": x, "y": y, "z": z}
L6["c"] = prod(y, b, y)
def conj_matrix(word):
    S = [[const(1), {}], [{}, const(1)]]; dinv = const(1)
    for ch in word:
        S = mmul(S, L6[ch]); dinv = mul(dinv, detinv[ch])
    Sadj = adj(S)
    return [coeffs_of([[mul(dinv, v) for v in row] for row in mmul(mmul(S, E[i]), Sadj)]) for i in range(4)]
def Fnullvec(rows, n):
    A = [r[:] for r in rows]; piv_cols = []; r = 0
    for col in range(n):
        pr = next((i for i in range(r, len(A)) if A[i][col] != ZERO), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        ip = Finv(A[r][col]); A[r] = [Fmul(ip, v) for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][col] != ZERO:
                f = A[i][col]; A[i] = [Fadd(A[i][k], Fneg(Fmul(f, A[r][k]))) for k in range(n)]
        piv_cols.append(col); r += 1
    free = [col for col in range(n) if col not in piv_cols]
    assert len(free) == 1, ("nullspace dim", len(free))
    fc = free[0]; vec = [ZERO] * n; vec[fc] = ONE
    for i, pc in enumerate(piv_cols):
        vec[pc] = Fneg(A[i][fc])
    return vec
def beta_for(word):
    C = conj_matrix(word)
    rows = []
    for i in range(4):
        for l in range(4):
            row = []
            for k in range(4):
                t = c[k][i][l]
                for j in range(4):
                    t = Fadd(t, Fneg(Fmul(C[i][j], c[j][k][l])))
                row.append(t)
            rows.append(row)
    return Fnullvec(rows, 4)
# 2-adic evaluation at q': w = 2u, 4u^2 - u - 1 = 0
P = 70; MOD = 1 << P
u = 1
for k in range(1, P + 2):
    if (4 * u * u - u - 1) % (1 << (k + 1)):
        u += 1 << k
W2 = 2 * (u % MOD)
def ev(p):
    return p[0] + p[1] * W2
def v2(q):
    if q == 0:
        return 10**6
    n, d = q.numerator, q.denominator; v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
BIG = P - 12
def Lmat(bvec):  # left multiplication on B in basis e, evaluated at q'
    return [[sum(ev(bvec[i]) * ev(c[i][k][l]) for i in range(4)) for k in range(4)] for l in range(4)]
def Rmat(bvec):  # right multiplication by beta
    return [[sum(ev(bvec[i]) * ev(c[k][i][l]) for i in range(4)) for k in range(4)] for l in range(4)]
tvec = [ev(in_F(tr(E[k]))) for k in range(4)]
Tq = [[ev(T[i][j]) for j in range(4)] for i in range(4)]
def nrd(bv):
    tb = sum(bv[k] * tvec[k] for k in range(4))
    q = sum(bv[i] * Tq[i][j] * bv[j] for i in range(4) for j in range(4))
    return (tb * tb - q) / 2
def sqrt2(xq):
    v = v2(xq)
    if v % 2: return None
    uu = xq / Fr(2) ** v
    num = (uu.numerator * pow(uu.denominator, -1, MOD)) % MOD
    if num % 8 != 1: return None
    r = 1
    for k in range(3, P):
        if (r * r - num) % (1 << (k + 1)):
            r += 1 << (k - 1)
    return Fr(r) * Fr(2) ** (v // 2)
zd = None
for b0 in range(-3, 4):
    for b1 in range(-3, 4):
        for b2 in range(-3, 4):
            f0 = nrd([Fr(b0), Fr(b1), Fr(b2), Fr(0)]); f1 = nrd([Fr(b0), Fr(b1), Fr(b2), Fr(1)]); fm = nrd([Fr(b0), Fr(b1), Fr(b2), Fr(-1)])
            A2 = (f1 + fm) / 2 - f0; B1 = (f1 - fm) / 2; C0 = f0
            if A2 == 0: continue
            D = B1 * B1 - 4 * A2 * C0
            sd = sqrt2(D)
            if sd is None: continue
            b3 = (-B1 + sd) / (2 * A2)
            zd = [Fr(b0), Fr(b1), Fr(b2), b3]; break
        if zd: break
    if zd: break
print("zero divisor found:", zd is not None, " v2(nrd) =", v2(nrd(zd)))
# left ideal B*n: columns of R(n); choose two independent columns
Rn = [[sum(zd[i] * ev(c[k][i][l]) for i in range(4)) for k in range(4)] for l in range(4)]
cols = [[Rn[l][k] for l in range(4)] for k in range(4)]
def indep(u1, u2):
    return any(v2(u1[i] * u2[j] - u1[j] * u2[i]) < BIG for i in range(4) for j in range(4))
u1 = next(cv for cv in cols if min(v2(t) for t in cv) < BIG)
u2 = next(cv for cv in cols if indep(u1, cv))
def rep2(bvec):  # 2x2 matrix of left multiplication by beta on span(u1,u2)
    Lb = Lmat(bvec)
    def apply(uv): return [sum(Lb[l][k] * uv[k] for k in range(4)) for l in range(4)]
    out = []
    for uv in (u1, u2):
        img = apply(uv)
        # solve img = p u1 + q u2 using a 2x2 minor with small valuation
        best = None
        for i in range(4):
            for j in range(4):
                dmin = u1[i] * u2[j] - u1[j] * u2[i]
                if best is None or v2(dmin) < v2(best[0]): best = (dmin, i, j)
        dmin, i, j = best
        p_ = (img[i] * u2[j] - img[j] * u2[i]) / dmin; q_ = (u1[i] * img[j] - u1[j] * img[i]) / dmin
        out.append((p_, q_))
    return ((out[0][0], out[1][0]), (out[0][1], out[1][1]))
def gl2(bvec):
    Mx = rep2(bvec); return (Mx[0][0], Mx[0][1], Mx[1][0], Mx[1][1])
exec(open("radu-second-tree-part2.py").read())
