"""Maslov-triple flux engine test at p = 3 versus p = 5.

The flux of the capstone route lives, correctly framed, in the
Lion--Vergne / Maslov-triple mechanism: the composite of the three
canonical intertwiners around a triple of polarizations is a scalar
(Schur), and the scalar is a Weil-index Gauss-sum quotient whose
arithmetic is the Hilbert-symbol class.  This script tests the
ARITHMETIC ENGINE on finite modules l^2(Z/p^k), p odd:

For g = [[a,b],[c,d]] in SL_2(Z/p^k) with c invertible, define the
explicit Weil-type kernel (one fixed convention, used identically for
every g and every p):

    (W(g) f)(u) = q^{-1/2} * sum_x psi( (a x^2 - 2 x u + d u^2) * inv(2c) ) f(x)

with psi(t) = e(t/q).  Each W(g) intertwines the standard Heisenberg
model with itself twisted by g, so for g1 g2 g3 = 1 (each with
invertible c) the composite W(g1) W(g2) W(g3) is scalar by Schur.
The scalar is the Weil cocycle triple product -- an 8th root of unity
class -- and the p = 3 versus p = 5 comparison is convention-free
because the code is identical.

Diagnostics (nontriviality witnesses -- run is VOID unless they pass):
  (i)  each W(g) is unitary to 1e-8;
  (ii) each W(g) intertwines: W(g) rho(v) W(g)^{-1} = phase * rho(g v)
       for Heisenberg generators v (checked up to scalar phase);
  (iii) the composite has nonscalarity < 1e-8.

Triples tested: (w, [[1,-1],[1,0]], [[1,0],[1,1]]) whose product is 1,
plus a second independent triple, plus levels k = 3, 4 for stability.
"""
import numpy as np


def e(x):
    return np.exp(2j * np.pi * x)


def weil_kernel(g, q):
    a, b, c, d = g
    cinv2 = pow((2 * c) % q, -1, q)
    x = np.arange(q)
    u = x.reshape(-1, 1)
    ph = ((a * x * x - 2 * x * u + d * u * u) % q) * cinv2 % q
    return e(ph / q) / np.sqrt(q)


def heis(q):
    X = np.zeros((q, q), dtype=complex)
    for x in range(q):
        X[x, (x - 1) % q] = 1.0
    Z = np.diag([e(x / q) for x in range(q)])
    return X, Z


def phase_dist(A, B):
    """distance from A to phase*B, minimized over the phase"""
    ip = np.vdot(B, A)
    if abs(ip) < 1e-14:
        return np.linalg.norm(A - B)
    ph = ip / abs(ip)
    return np.linalg.norm(A - ph * B)


def sl2_check(g, q):
    a, b, c, d = g
    assert (a * d - b * c) % q == 1 % q, f"det != 1 for {g} mod {q}"


def run_triple(p, k, gs, label):
    q = p ** k
    for g in gs:
        sl2_check(g, q)
    prod = np.eye(2, dtype=object)
    m = [[gs[0][0], gs[0][1]], [gs[0][2], gs[0][3]]]
    for g in gs[1:]:
        n = [[g[0], g[1]], [g[2], g[3]]]
        m = [[(m[0][0] * n[0][0] + m[0][1] * n[1][0]) % q,
              (m[0][0] * n[0][1] + m[0][1] * n[1][1]) % q],
             [(m[1][0] * n[0][0] + m[1][1] * n[1][0]) % q,
              (m[1][0] * n[0][1] + m[1][1] * n[1][1]) % q]]
    assert m == [[1 % q, 0], [0, 1 % q]], f"product not identity: {m}"

    X, Z = heis(q)
    Ws = [weil_kernel(g, q) for g in gs]
    diag = []
    for g, W in zip(gs, Ws):
        unit = np.linalg.norm(W @ W.conj().T - np.eye(q))
        a, b, c, d = g
        # g acts on Heisenberg coords (m, n) -> (a m + b n, c m + d n)
        # rho(m, n) = X^m Z^n up to phase; check on the two generators
        tX = np.linalg.matrix_power(X, a % q) @ np.linalg.matrix_power(Z, c % q)
        tZ = np.linalg.matrix_power(X, b % q) @ np.linalg.matrix_power(Z, d % q)
        iX = phase_dist(W @ X @ W.conj().T, tX)
        iZ = phase_dist(W @ Z @ W.conj().T, tZ)
        diag.append((unit, iX, iZ))
    C = Ws[0] @ Ws[1] @ Ws[2]
    sc = np.trace(C) / q
    nonsc = np.linalg.norm(C - sc * np.eye(q)) / np.sqrt(q)
    arg8 = np.angle(sc) / (2 * np.pi) * 8
    print(f"p={p} k={k} [{label}]: scalar {sc:.6f} |.|={abs(sc):.4f} "
          f"arg = {arg8:+.4f} eighths, nonscalarity={nonsc:.2e}", flush=True)
    for g, (unit, iX, iZ) in zip(gs, diag):
        print(f"    g={g}: unitarity={unit:.2e} intertwine X={iX:.2e} Z={iZ:.2e}",
              flush=True)


T1 = [(0, 1, -1, 0), (1, -1, 1, 0), (1, 0, 1, 1)]
T2 = [(0, 1, -1, 0), (2, -1, 1, 0), (1, 0, 2, 1)]  # second triple, product 1
for p in (3, 5):
    for k in (3, 4):
        for gs, label in ((T1, "T1"), (T2, "T2")):
            gs_mod = [tuple(v % (p ** k) for v in g) for g in gs]
            run_triple(p, k, gs_mod, label)
print("MASLOV-TRIPLE-DONE")
