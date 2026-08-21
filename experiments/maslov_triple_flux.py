"""Maslov-triple flux engine test at p = 3 versus p = 5 (v2).

Composite of three canonical metaplectic kernels around a product-one
triple in SL_2(Z/p^k); the composite is scalar by Schur once each
kernel genuinely intertwines, and the scalar's 8th-root class is the
Weil-cocycle triple product.  Identical code at both primes makes the
p = 3 vs p = 5 comparison convention-free.

v2 fixes the v1 convention failure (witnesses rejected the kernels):
  * Heisenberg: (Xf)(x) = f(x-1), Z = diag e(x/q); then F with kernel
    e(-ux/q)/sqrt(q) satisfies Ad(F): X -> Z^{-1}, Z -> X, i.e. F
    implements g_F = [[0,1],[-1,0]] on COLUMN vectors (m,n) with
    rho(m,n) = X^m Z^n.
  * Weyl-symmetrized operators rho_W(m,n) = e(2bar*m*n/q) X^m Z^n
    make the intertwining phase-free at odd p, so the witness is
    W rho_W(v) W* = rho_W(g v) with NO phase allowance.
  * Kernel for g = [[a,b],[c,d]], c invertible:
        K(u,x) = q^{-1/2} psi( -2bar * c^{-1} * (a x^2 - 2 u x + d u^2) )
    A programmatic convention search over the exponent sign is run
    first and REPORTED; the run is VOID unless exactly one sign
    passes all witnesses at 1e-8.
"""
import numpy as np


def e(x):
    return np.exp(2j * np.pi * x)


def heis(q):
    X = np.zeros((q, q), dtype=complex)
    for x in range(q):
        X[x, (x - 1) % q] = 1.0
    Z = np.diag([e(x / q) for x in range(q)])
    return X, Z


def rho_w(q, m, n, X, Z):
    inv2 = pow(2, -1, q)
    ph = e(((inv2 * m * n) % q) / q)
    return ph * np.linalg.matrix_power(X, m % q) @ np.linalg.matrix_power(Z, n % q)


def weil_kernel(g, q, sign):
    a, b, c, d = g
    cinv = pow(c % q, -1, q)
    inv2 = pow(2, -1, q)
    x = np.arange(q)
    u = x.reshape(-1, 1)
    quad = (a * x * x - 2 * u * x + d * u * u) % q
    ph = (sign * inv2 * cinv % q) * quad % q
    return e(ph / q) / np.sqrt(q)


def witness(W, g, q, X, Z):
    """max over the two generators of || W rho_W(v) W* - rho_W(g v) ||"""
    a, b, c, d = g
    errs = []
    for (m, n) in ((1, 0), (0, 1)):
        gm, gn = (a * m + b * n) % q, (c * m + d * n) % q
        lhs = W @ rho_w(q, m, n, X, Z) @ W.conj().T
        rhs = rho_w(q, gm, gn, X, Z)
        errs.append(np.linalg.norm(lhs - rhs))
    return max(errs)


def matmul2(m, n, q):
    return [[(m[0][0] * n[0][0] + m[0][1] * n[1][0]) % q,
             (m[0][0] * n[0][1] + m[0][1] * n[1][1]) % q],
            [(m[1][0] * n[0][0] + m[1][1] * n[1][0]) % q,
             (m[1][0] * n[0][1] + m[1][1] * n[1][1]) % q]]


def run_triple(p, k, gs, label, sign):
    q = p ** k
    prod = [[1, 0], [0, 1]]
    for g in gs:
        assert (g[0] * g[3] - g[1] * g[2]) % q == 1 % q, f"det!=1: {g}"
        prod = matmul2(prod, [[g[0], g[1]], [g[2], g[3]]], q)
    assert prod == [[1 % q, 0], [0, 1 % q]], f"product not identity: {prod}"
    X, Z = heis(q)
    Ws, wits = [], []
    for g in gs:
        W = weil_kernel(g, q, sign)
        Ws.append(W)
        wits.append(witness(W, g, q, X, Z))
    C = Ws[0] @ Ws[1] @ Ws[2]
    sc = np.trace(C) / q
    nonsc = np.linalg.norm(C - sc * np.eye(q)) / np.sqrt(q)
    arg8 = np.angle(sc) / (2 * np.pi) * 8
    ok = max(wits) < 1e-8 and nonsc < 1e-8
    print(f"p={p} k={k} [{label}]: scalar {sc:.6f} |.|={abs(sc):.4f} "
          f"arg={arg8:+.4f}/8  nonscalarity={nonsc:.2e} "
          f"witness={max(wits):.2e} {'OK' if ok else 'VOID'}", flush=True)
    return ok


# convention search at small level: exactly one sign must pass
print("== convention search (p=3, k=2) ==", flush=True)
passing = []
for sign in (1, -1):
    q = 9
    X, Z = heis(q)
    g = (0, 1, -1 % q, 0)
    W = weil_kernel(g, q, sign)
    err = witness(W, g, q, X, Z)
    print(f"  sign={sign:+d}: witness={err:.2e}", flush=True)
    if err < 1e-8:
        passing.append(sign)
if len(passing) != 1:
    print(f"CONVENTION SEARCH FAILED: passing={passing} -- RUN VOID", flush=True)
    raise SystemExit(1)
SIGN = passing[0]
print(f"== canonical sign: {SIGN:+d} ==", flush=True)

T1 = [(0, 1, -1, 0), (1, -1, 1, 0), (1, 0, 1, 1)]
T2 = [(0, 1, -1, 0), (2, -1, 1, 0), (1, 0, 2, 1)]
allok = True
for p in (3, 5):
    for k in (3, 4):
        for gs, label in ((T1, "T1"), (T2, "T2")):
            gs_mod = [tuple(v % (p ** k) for v in g) for g in gs]
            allok &= run_triple(p, k, gs_mod, label, SIGN)
print("MASLOV-TRIPLE-DONE" + ("" if allok else " (SOME VOID)"))
