#!/usr/bin/env python3
"""Checks for research/artifacts/sp4-schur-deligne-packet-pruning-2026-09-16.md.

E1  Bianchi embedding.  For O_d = Z[omega], the form
        beta(u, v) = Im(u1 v2 - u2 v1) / Im(omega)
    on O_d^2 is integral, alternating and unimodular in the Z-basis
    e1=(1,0), e2=(omega,0), e3=(0,1), e4=(0,omega).  The generators
    [[1,1],[0,1]], [[1,omega],[0,1]], [[0,-1],[1,0]] of SL_2(O_d) act by
    integer 4x4 matrices of determinant 1 preserving beta, and the basis
    (e1, e2 - t e1, e4, e3), t = tr(omega), is a symplectic basis.
    Exact arithmetic (sympy).

E2  Windings.  For closed loops M(theta) in Sp_4(R) (standard form
    J = [[0,I],[-I,0]]), the orthogonal polar factor O = M (M^T M)^(-1/2)
    lies in K = U(2), O = [[X,-Y],[Y,X]] <-> X + iY, and the winding of
    det(X + iY) is the class of the loop in pi_1(Sp_4(R)) = Z.  Numerics.

E3  Klingen radical.  The central element m(1,-I) of the Klingen Levi acts
    by -1 on the non-central part of the Heisenberg Lie algebra and by +1 on
    its center.  Exact arithmetic.

    E2 also treats D^1 = SL_2(R) acting on M_2(R) by left multiplication with
    the invariant alternating form B_mu(x,y) = tr(adj(x) y mu): winding +-2
    for mu = [[0,-1],[1,0]] (nrd mu > 0) and 0 for mu = diag(1,-1)
    (nrd mu < 0).
"""
import numpy as np
import sympy as sp

OK = True


def report(name, cond, extra=""):
    global OK
    OK = OK and bool(cond)
    print(("PASS " if cond else "FAIL ") + name + (" " + extra if extra else ""))


# ---------------------------------------------------------------- E1
def omega_of(d):
    return sp.sqrt(-d) if d % 4 in (1, 2) else (1 + sp.sqrt(-d)) / 2


def e1_bianchi(d):
    w = omega_of(d)
    basis = [(sp.Integer(1), sp.Integer(0)), (w, sp.Integer(0)),
             (sp.Integer(0), sp.Integer(1)), (sp.Integer(0), w)]
    imw = sp.im(w)

    def beta(u, v):
        return sp.nsimplify(sp.simplify(sp.im(sp.expand(u[0] * v[1] - u[1] * v[0])) / imw))

    G = sp.Matrix(4, 4, lambda i, j: beta(basis[i], basis[j]))
    t = sp.simplify(w + sp.conjugate(w))
    n = sp.simplify(w * sp.conjugate(w))
    integral = all(x.is_integer for x in G)
    alternating = (G.T == -G)
    det = G.det()
    report(f"E1 d={d} Gram integral/alternating/unimodular", integral and alternating and det == 1,
           f"t={t} N={n} G={G.tolist()} det={det}")

    # coordinates of a in O_d as a + b*omega
    def coords(a):
        a = sp.expand(a)
        b = sp.simplify(sp.im(a) / imw)
        c = sp.simplify(sp.re(a) - b * sp.re(w))
        assert c.is_integer and b.is_integer, (a, c, b)
        return c, b

    def int_matrix(g):
        cols = []
        for (x1, x2) in basis:
            y1 = sp.expand(g[0][0] * x1 + g[0][1] * x2)
            y2 = sp.expand(g[1][0] * x1 + g[1][1] * x2)
            c1, b1 = coords(y1)
            c2, b2 = coords(y2)
            cols.append([c1, b1, c2, b2])
        return sp.Matrix(cols).T

    gens = {"U1": [[1, 1], [0, 1]], "Uw": [[1, w], [0, 1]], "S": [[0, -1], [1, 0]]}
    for name, g in gens.items():
        g = [[sp.sympify(x) for x in row] for row in g]
        M = int_matrix(g)
        pres = sp.simplify(M.T * G * M - G) == sp.zeros(4, 4)
        report(f"E1 d={d} generator {name} integral, det 1, preserves beta",
               all(x.is_integer for x in M) and M.det() == 1 and pres)
    P = sp.Matrix([[1, 0, 0, 0], [-t, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]).T  # columns e1, e2-t e1, e4, e3
    J = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]])
    report(f"E1 d={d} (e1, e2-t e1, e4, e3) is a symplectic Z-basis",
           sp.simplify(P.T * G * P - J) == sp.zeros(4, 4) and abs(P.det()) == 1)


# ---------------------------------------------------------------- E2
J4 = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])


def rot(th):
    return np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])


def polar_O(M):
    w, V = np.linalg.eigh(M.T @ M)
    return M @ V @ np.diag(w ** -0.5) @ V.T


def winding(loop, N=2000, form=J4):
    phases = []
    for th in np.linspace(0.0, 2 * np.pi, N + 1):
        M = loop(th)
        assert np.allclose(M.T @ form @ M, form, atol=1e-9), "not symplectic"
        O = polar_O(M)
        X, Y = O[:2, :2], O[2:, :2]
        assert np.allclose(O, np.block([[X, -Y], [Y, X]]), atol=1e-8)
        phases.append(np.angle(np.linalg.det(X + 1j * Y)))
    ph = np.unwrap(np.array(phases))
    return (ph[-1] - ph[0]) / (2 * np.pi)


def embed_pairs(A, B):
    """A acts on span(e1,f1), B on span(e2,f2); basis order (e1,e2,f1,f2)."""
    M = np.zeros((4, 4))
    idx1, idx2 = [0, 2], [1, 3]
    for i in range(2):
        for j in range(2):
            M[idx1[i], idx1[j]] = A[i, j]
            M[idx2[i], idx2[j]] = B[i, j]
    return M


def sym3(g):
    """Action of g in SL_2(R) on binary cubics, basis x^3, x^2 y, x y^2, y^3:
    the monomial x^i y^(3-i) goes to (a x + c y)^i (b x + d y)^(3-i)."""
    a, b, c, d = g[0, 0], g[0, 1], g[1, 0], g[1, 1]
    lin_x = np.array([c, a])  # coefficients indexed by power of x: c*y + a*x
    lin_y = np.array([d, b])
    M = np.zeros((4, 4))
    for j, i in enumerate((3, 2, 1, 0)):
        p = np.array([1.0])
        for _ in range(i):
            p = np.convolve(p, lin_x)
        for _ in range(3 - i):
            p = np.convolve(p, lin_y)
        for r, k in enumerate((3, 2, 1, 0)):
            M[r, j] = p[k]
    return M


def principal_loop_and_form():
    # invariant alternating form on Sym^3: <x^3, y^3> = 1, <x^2 y, x y^2> = -1/3
    W = np.zeros((4, 4))
    W[0, 3], W[3, 0] = 1.0, -1.0
    W[1, 2], W[2, 1] = -1.0 / 3, 1.0 / 3
    for g in (np.array([[2.0, 1.0], [1.0, 1.0]]), rot(0.7), np.array([[1.0, 0.0], [3.0, 1.0]])):
        M = sym3(g)
        assert np.allclose(M.T @ W @ M, W, atol=1e-9), "principal form not invariant"
    # Darboux change of basis: find P with P^T W P = J4
    P = darboux(W)
    Pinv = np.linalg.inv(P)
    return (lambda th: Pinv @ sym3(rot(th)) @ P), W, P


def darboux(W):
    n = W.shape[0]
    vecs = [np.eye(n)[i] for i in range(n)]
    es, fs = [], []
    rest = vecs[:]
    while rest:
        e = rest.pop(0)
        if any(abs(e @ W @ v) > 1e-12 for v in rest):
            k = max(range(len(rest)), key=lambda i: abs(e @ W @ rest[i]))
            f = rest.pop(k)
            f = f / (e @ W @ f)
            def proj(v):
                return v - (v @ W @ f) * e + (v @ W @ e) * f
            rest = [proj(v) for v in rest]
            rest = [v for v in rest if np.linalg.norm(v) > 1e-12]
            es.append(e)
            fs.append(f)
    P = np.column_stack(es + fs)
    assert np.allclose(P.T @ W @ P, J4, atol=1e-9)
    return P


def sl2c_loop():
    # C^2 = R^4 with real coordinates (Re u1, Im u1, Re u2, Im u2); form Im det
    def realify(g):
        M = np.zeros((4, 4))
        for j in range(4):
            v = np.zeros(4)
            v[j] = 1.0
            u = np.array([v[0] + 1j * v[1], v[2] + 1j * v[3]])
            gu = g @ u
            M[:, j] = [gu[0].real, gu[0].imag, gu[1].real, gu[1].imag]
        return M

    def imdet(v, w):
        u = np.array([v[0] + 1j * v[1], v[2] + 1j * v[3]])
        z = np.array([w[0] + 1j * w[1], w[2] + 1j * w[3]])
        return (u[0] * z[1] - u[1] * z[0]).imag

    W = np.array([[imdet(np.eye(4)[i], np.eye(4)[j]) for j in range(4)] for i in range(4)])
    P = darboux(W)
    Pinv = np.linalg.inv(P)
    return lambda th: Pinv @ realify(np.array([[np.exp(1j * th), 0], [0, np.exp(-1j * th)]])) @ P


def quaternion_loop(mu):
    # D^1 = SL_2(R) acting on M_2(R) = R^2 + R^2 (columns a, b) by g (a|b) = (ga|gb).
    def adj(x):
        return np.array([[x[1, 1], -x[0, 1]], [-x[1, 0], x[0, 0]]])

    def vec2mat(v):
        return np.array([[v[0], v[2]], [v[1], v[3]]])  # columns a=(v0,v1), b=(v2,v3)

    W = np.array([[np.trace(adj(vec2mat(np.eye(4)[i])) @ vec2mat(np.eye(4)[j]) @ mu)
                   for j in range(4)] for i in range(4)])
    assert np.allclose(W, -W.T)
    P = darboux(W)
    Pinv = np.linalg.inv(P)
    return lambda th: Pinv @ np.kron(np.eye(2), rot(th)) @ P


def e2_windings():
    tests = []
    tests.append(("standard block SL_2 on (e1,f1)", lambda th: embed_pairs(rot(th), np.eye(2)), {1, -1}))
    tests.append(("Klingen Levi SL_2 on (e2,f2)", lambda th: embed_pairs(np.eye(2), rot(th)), {1, -1}))
    tests.append(("diagonal g+g in omega+omega", lambda th: embed_pairs(rot(th), rot(th)), {2, -2}))
    tests.append(("diagonal g+g in omega+(-omega)", lambda th: embed_pairs(rot(th), rot(-th)), {0}))
    tests.append(("Siegel Levi diag(A, A^-T), A = rot", lambda th: np.block([[rot(th), np.zeros((2, 2))], [np.zeros((2, 2)), rot(th)]]), {0}))

    def siegel_noncompact(th):
        A = np.diag([2.0, 0.5]) @ rot(th) @ np.diag([1.0 + 0.5 * np.sin(th), 1.0 / (1.0 + 0.5 * np.sin(th))])
        S = np.array([[np.cos(th), np.sin(2 * th)], [np.sin(2 * th), 3.0]])
        return np.block([[A, A @ S], [np.zeros((2, 2)), np.linalg.inv(A).T]])

    tests.append(("Siegel parabolic non-compact loop", siegel_noncompact, {0}))
    ploop, _, _ = principal_loop_and_form()
    tests.append(("principal Sym^3", ploop, None))
    tests.append(("SL_2(C) torus diag(e^it, e^-it), form Im det", sl2c_loop(), {0}))
    tests.append(("quaternion D^1, mu = [[0,-1],[1,0]] (nrd>0)", quaternion_loop(np.array([[0.0, -1.0], [1.0, 0.0]])), {2, -2}))
    tests.append(("quaternion D^1, mu = diag(1,-1) (nrd<0)", quaternion_loop(np.diag([1.0, -1.0])), {0}))
    for name, loop, expected in tests:
        wnd = winding(loop)
        r = int(round(wnd))
        good = abs(wnd - r) < 1e-6 and (expected is None or r in expected)
        report(f"E2 winding {name}", good, f"= {wnd:.6f}")


# ---------------------------------------------------------------- E3
def e3_klingen():
    # basis (e1, e2, f1, f2); Klingen = stabilizer of the line R e1.
    s = sp.symbols("p q c")
    p, q, c = s
    # unipotent radical Lie algebra: X e1 = 0, X e2 = ?, etc.  Generic element of
    # the nilradical n of the Klingen parabolic inside sp_4.
    X = sp.zeros(4, 4)
    # X f1 = p e2 + q f2 + c e1 ; X e2 = -q e1 ... enforce X^T J + J X = 0
    a = sp.symbols("a0:16")
    Xg = sp.Matrix(4, 4, a)
    J = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]])
    eqs = list(Xg.T * J + J * Xg)
    e1 = sp.Matrix([1, 0, 0, 0])
    perp = [sp.Matrix([1, 0, 0, 0]), sp.Matrix([0, 1, 0, 0]), sp.Matrix([0, 0, 0, 1])]
    # nilradical: X e1 = 0, X(e1^perp) in R e1, X(V) in e1^perp
    eqs += list(Xg * e1)
    for v in perp[1:]:
        eqs += list((Xg * v)[1:, :])
    eqs += [(Xg * sp.Matrix([0, 0, 1, 0]))[2]]
    sol = sp.solve(eqs, a, dict=True)[0]
    Xn = Xg.subs(sol)
    free = sorted(Xn.free_symbols, key=str)
    m = sp.diag(1, -1, 1, -1)  # m(1, -I): identity on (e1,f1), -I on (e2,f2)
    conj = m * Xn * m.inv()
    # center of n: maps f1 -> c e1
    center = [x for x in free if (Xn.subs({y: 0 for y in free if y != x}) * sp.Matrix([0, 1, 0, 0])) == sp.zeros(4, 1)
              and (Xn.subs({y: 0 for y in free if y != x}) * sp.Matrix([0, 0, 0, 1])) == sp.zeros(4, 1)]
    ok = True
    for x in free:
        Xi = Xn.subs({y: (1 if y == x else 0) for y in free})
        Ci = m * Xi * m.inv()
        sign = 1 if Ci == Xi else (-1 if Ci == -Xi else None)
        expect = 1 if x in center else -1
        ok = ok and sign == expect
        print(f"   n-basis {x}: m(1,-I) acts by {sign} ({'center' if x in center else 'non-central'})")
    report("E3 dim n = 3, center dim 1", len(free) == 3 and len(center) == 1)
    report("E3 m(1,-I) acts by -1 on n/center and +1 on center", ok)

    # group level: n(a,b,c): e1->e1, e2->e2+a e1, f2->f2+b e1, f1->f1+c e1+b e2-a f2
    def n_el(a, b, c):
        M = sp.eye(4)  # columns are images of (e1, e2, f1, f2)
        M[:, 1] = sp.Matrix([a, 1, 0, 0])
        M[:, 3] = sp.Matrix([b, 0, 0, 1])
        M[:, 2] = sp.Matrix([c, b, 1, -a])
        return M
    A, Bs, Cs, A2, B2, C2 = sp.symbols("A B C A2 B2 C2")
    Mn = n_el(A, Bs, Cs)
    report("E3 n(a,b,c) is symplectic for all a,b,c", sp.simplify(Mn.T * J * Mn - J) == sp.zeros(4, 4))
    prod = sp.simplify(n_el(A, Bs, Cs) * n_el(A2, B2, C2))
    comm = sp.simplify(n_el(1, 0, 0) * n_el(0, 1, 0) * n_el(1, 0, 0).inv() * n_el(0, 1, 0).inv())
    report("E3 [n(1,0,0), n(0,1,0)] = n(0,0,c) with c != 0", comm == n_el(0, 0, comm[0, 2]) and comm[0, 2] != 0,
           f"c={comm[0, 2]}")
    closed = sp.simplify(prod - n_el(A + A2, Bs + B2, prod[0, 2])) == sp.zeros(4, 4)
    report("E3 n(a,b,c) n(a',b',c') = n(a+a', b+b', *)", closed, f"* = {sp.expand(prod[0, 2])}")
    report("E3 m(1,-I) n(a,b,c) m(1,-I)^-1 = n(-a,-b,c)", sp.simplify(m * Mn * m.inv() - n_el(-A, -Bs, Cs)) == sp.zeros(4, 4))


# ---------------------------------------------------------------- main
if __name__ == "__main__":
    for d in (1, 2, 3, 7, 11, 15, 19):
        e1_bianchi(d)
    e2_windings()
    e3_klingen()
    print("ALL PASS" if OK else "SOME FAILED")
