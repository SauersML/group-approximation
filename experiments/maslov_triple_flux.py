"""Metaplectic anomaly classes at p = 3 versus p = 5 (v3).

v1/v2 autopsy: general-entry Weil kernel formulas kept failing their
intertwining witnesses.  v3 eliminates formula risk entirely: only
VERIFIED PRIMITIVES are used, each a fixed concrete matrix with no
normalization freedom, so every reported scalar is fully canonical.

Primitives on l^2(Z/q), q = p^k, p odd:
  F0      kernel e(-ux/q)/sqrt(q)      implements [[0,1],[-1,0]]
  mult(t) diag e(2bar t x^2 / q)       implements [[1,0],[t,1]]
  P       (Pf)(x) = f(-x)              implements -I
Witnesses (phase-free against Weyl-symmetrized rho_W(m,n) =
e(2bar mn/q) X^m Z^n): each primitive must intertwine at 1e-8, and
each anomaly word must be scalar at 1e-8, else the line is VOID.

Anomaly words (all products equal to the identity or -I in SL_2, so
the operators are scalar (resp. scalar times the exactly-known P)):
  F0^4                      = I in SL_2      -> control, expect exactly 1
  A(t) = (F0 mult(t))^3 P   = I in SL_2      -> the metaplectic anomaly;
        (W0 M(1))^3 = -I classically, P accounts for -I, so A(t) is a
        canonical 8th-root-of-unity class (the Gauss-sum cocycle).
Report A(t) for t in {1, -1, 2} across p in {3,5}, k in {2,3,4,5};
the p = 3 vs p = 5 and k-parity pattern is the flux-arithmetic
signature (epsilon_q alternates at p = 3, constant at p = 5).
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
    ph = e(((inv2 * (m % q) * (n % q)) % q) / q)
    return ph * np.linalg.matrix_power(X, m % q) @ np.linalg.matrix_power(Z, n % q)


def witness(W, g, q, X, Z):
    a, b, c, d = g
    errs = []
    for (m, n) in ((1, 0), (0, 1)):
        gm, gn = (a * m + b * n) % q, (c * m + d * n) % q
        errs.append(np.linalg.norm(W @ rho_w(q, m, n, X, Z) @ W.conj().T
                                   - rho_w(q, gm, gn, X, Z)))
    return max(errs)


def run(p, k):
    q = p ** k
    inv2 = pow(2, -1, q)
    X, Z = heis(q)
    x = np.arange(q)
    F0 = e(-(np.outer(x, x) % q) / q) / np.sqrt(q)
    P = np.zeros((q, q))
    P[x, (-x) % q] = 1.0

    wF = witness(F0, (0, 1, -1, 0), q, X, Z)
    wP = witness(P, (-1, 0, 0, -1), q, X, Z)

    ctrl = np.linalg.matrix_power(F0, 4)
    c_sc = np.trace(ctrl) / q
    c_ns = np.linalg.norm(ctrl - c_sc * np.eye(q)) / np.sqrt(q)
    print(f"p={p} k={k} (q={q}): primitives wF={wF:.1e} wP={wP:.1e}; "
          f"F0^4 scalar {c_sc:.6f} nonsc={c_ns:.1e}", flush=True)

    # (W0 M(1))^3 = -I (order 6, trace 1) -> word needs P;
    # (W0 M(-1))^3 = +I (order 3, trace -1) -> word is the bare cube.
    scs = {}
    for t, use_p in ((1, True), (-1, False)):
        M = np.diag(e(((inv2 * t % q) * (x * x) % q) / q))
        wM = witness(M, (1, 0, t % q, 1), q, X, Z)
        B = F0 @ M
        A = B @ B @ B
        if use_p:
            A = A @ P
        sc = np.trace(A) / q
        ns = np.linalg.norm(A - sc * np.eye(q)) / np.sqrt(q)
        ok = max(wM, wF, wP) < 1e-8 and ns < 1e-8 and abs(abs(sc) - 1) < 1e-8
        arg8 = np.angle(sc) / (2 * np.pi) * 8
        scs[t] = sc if ok else None
        print(f"    A({t:+d}): scalar {sc:+.6f} arg={arg8:+.4f}/8 "
              f"nonsc={ns:.1e} wM={wM:.1e} {'OK' if ok else 'VOID'}",
              flush=True)
    if scs[1] is not None and scs[-1] is not None:
        ratio = scs[1] / scs[-1]
        arg8 = np.angle(ratio) / (2 * np.pi) * 8
        print(f"    class ratio A(+1)/A(-1): {ratio:+.6f} arg={arg8:+.4f}/8",
              flush=True)


for p in (3, 5):
    for k in (2, 3, 4, 5):
        if p ** k > 700:
            continue
        run(p, k)
print("ANOMALY-CLASSES-DONE")
