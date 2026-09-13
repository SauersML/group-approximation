# Constrained numeric search for PSL_2(C) representations of the Janzen-Wise lattice
#   <a,b,x,y | axay, a x^-1 b y^-1, a y^-1 b^-1 x^-1, b x b^-1 y^-1>
# with x, y of order 3 in PSL_2 (trace 1 in SL_2), every relator +-I.
# Gauge: x = diag(e^{i pi/3}, e^{-i pi/3}), y = [[p, ps-1],[1, s]], s = 1 - p.
import cmath, random, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
def mm(A, B):
    return (A[0]*B[0] + A[1]*B[2], A[0]*B[1] + A[1]*B[3], A[2]*B[0] + A[3]*B[2], A[2]*B[1] + A[3]*B[3])
def inv(A):
    d = A[0]*A[3] - A[1]*A[2]
    return (A[3]/d, -A[1]/d, -A[2]/d, A[0]/d)
def sl2(p, q, r):
    return (p, q, r, (1 + q*r)/p)
def solve(M, rhs):
    n = len(M)
    A = [M[i][:] + [rhs[i]] for i in range(n)]
    for c in range(n):
        piv = max(range(c, n), key=lambda r: abs(A[r][c]))
        if abs(A[piv][c]) < 1e-300:
            return None
        A[c], A[piv] = A[piv], A[c]
        for r in range(n):
            if r != c:
                f = A[r][c] / A[c][c]
                A[r] = [A[r][k] - f * A[c][k] for k in range(n + 1)]
    return [A[i][n] / A[i][i] for i in range(n)]
w6 = cmath.exp(1j * cmath.pi / 3)
def mats(v):
    p, a0, a1, a2, b0, b1, b2 = v
    X = (w6, 0, 0, 1 / w6)
    s = 1 - p
    Y = (p, p * s - 1, 1, s)
    return sl2(a0, a1, a2), sl2(b0, b1, b2), X, Y
def residual(v):
    A, B, X, Y = mats(v)
    Ai, Bi, Xi, Yi = inv(A), inv(B), inv(X), inv(Y)
    rels = [mm(mm(mm(A, X), A), Y), mm(mm(mm(A, Xi), B), Yi), mm(mm(mm(A, Yi), Bi), Xi), mm(mm(mm(B, X), Bi), Yi)]
    out = []
    for R in rels:
        out += [R[1], R[2], R[0] - R[3]]
    return out
sols = []
SOLV_hold = []
for trial in range(600):
    v = [complex(random.uniform(-2, 2), random.uniform(-2, 2)) for _ in range(7)]
    ok = False
    for it in range(100):
        try:
            F = residual(v)
        except ZeroDivisionError:
            break
        nrm = sum(abs(f)**2 for f in F) ** 0.5
        if nrm < 1e-13:
            ok = True
            break
        h = 1e-7
        J = []
        for j in range(7):
            w = v[:]; w[j] += h
            try:
                Fj = residual(w)
            except ZeroDivisionError:
                J = None
                break
            J.append([(Fj[i] - F[i]) / h for i in range(12)])
        if J is None:
            break
        JH = [[J[j][i].conjugate() for i in range(12)] for j in range(7)]
        N = [[sum(JH[p_][i] * J[q][i] for i in range(12)) + (1e-12 if p_ == q else 0) for q in range(7)] for p_ in range(7)]
        g = [-sum(JH[p_][i] * F[i] for i in range(12)) for p_ in range(7)]
        d = solve(N, g)
        if d is None:
            break
        v = [v[k] + d[k] for k in range(7)]
        if any(abs(z) > 1e6 for z in v):
            break
    if ok and SOLV_hold.append(v) is None:
        A, B, X, Y = mats(v)
        def trp(M): return M[0] + M[3]
        trs = {"tr a": trp(A), "tr b": trp(B), "tr ab": trp(mm(A, B)), "tr xy": trp(mm(X, Y)), "tr ax": trp(mm(A, X)), "tr bx": trp(mm(B, X))}
        key = tuple(round(abs(trs[k])**2, 5) for k in sorted(trs))
        if key not in [s_[0] for s_ in sols]:
            sols.append((key, trs))
SOLV = None
for key, trs in sols:
    print("C", {k: "%.10f%+.10fi" % (z.real, z.imag) for k, z in trs.items()})
print("constrained distinct solutions:", len(sols))
exec(open("jw_invariants_tail.py").read())
