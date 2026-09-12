"""Two-prime flux discriminator: the depth-shift holonomy of the Weyl
inversion on finite oscillator towers, at p = 3 versus p = 5.

The flux-identification lemma predicts the tower holonomy of the full-level
Weyl inversion around the canonical congruence-equivariant band transport
equals the Hilbert symbol (p,p)_p = (-1|p): NONTRIVIAL (-1) at p = 3,
TRIVIAL (+1) at p = 5.  The code is identical for both primes, so any
convention choice cancels in the p=3-vs-p=5 comparison.

Construction (all phase-canonical):
  * level q = p^k Heisenberg pair X_q (shift), Z_q (modulation);
  * u_q(t) = multiplication by e(inv2 * t * x^2 / q)  -- a genuine
    homomorphism in t, no phase freedom once the additive character is fixed;
  * l_q(s) := F_q u_q(s) F_q^{-1}  -- conjugation kills the DFT phase;
  * w_q := u_q(1) l_q(-1) u_q(1)  -- the canonical Weyl inversion; the
    Gauss-sum (Weil index) anomaly is INSIDE this operator.  (The vacuous
    p=2 run used the plain DFT, whose F^4 = 1 leaves nothing to detect.)
  * T : level q -> level Q = p^(k-2), the canonical band transport, computed
    as the minimal-singular-vector solution of the JOINT intertwining system
        T X_q^p   = X_Q T,   T Z_q^p   = Z_Q T,
        T u_q(p^2) = u_Q(1) T,  T l_q(p^2) = l_Q(1) T,
    then row-polar-normalized to a coisometry.  Joint equivariance for the
    congruence copy pins T up to ONE phase (report the singular gap as the
    Schur-uniqueness check), and that phase cancels in the loop below
    because T appears once forward and once backward.

Holonomy:  L := rho_Q(w)^{-1} . T . rho_q(w) . T*   (Q x Q).
Report: loop scalar tr(L)/Q, its modulus and phase, nonscalarity
||L - scalar||_HS/sqrt(Q), the intertwining residuals, the singular gap,
and the w-diagnostics (dist of w X w^{-1} to Z^{+-1}, scalar of w^4).
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


def inv2(q):
    return pow(2, -1, q)


def u_op(q, t):
    i2 = inv2(q)
    return np.diag([e((i2 * t * x * x) % q / q) for x in range(q)])


def dft(q):
    j = np.arange(q)
    return e(np.outer(j, j) / q) / np.sqrt(q)


def weil_ops(q):
    F = dft(q)
    Fi = F.conj().T
    u1 = u_op(q, 1)
    lm1 = F @ u_op(q, -1) @ Fi
    w = u1 @ lm1 @ u1
    return w


def solve_transport(q, Q, p):
    """Min-singular solution T (Q x q) of the joint congruence system."""
    Xq, Zq = heis(q)
    XQ, ZQ = heis(Q)
    F_q, F_Q = dft(q), dft(Q)
    uq = u_op(q, p * p)
    uQ = u_op(Q, 1)
    lq = F_q @ u_op(q, -(p * p)) @ F_q.conj().T
    lQ = F_Q @ u_op(Q, -1) @ F_Q.conj().T
    # unknown T in C^{Q x q}; constraint  B T - T A = 0  vectorizes to
    # (I_q kron B - A^T kron I_Q) vec(T) = 0   with vec column-major.
    pairs = [
        (np.linalg.matrix_power(Xq, p), XQ),
        (np.linalg.matrix_power(Zq, p), ZQ),
        (uq, uQ),
        (lq, lQ),
    ]
    blocks = []
    for A, B in pairs:
        blocks.append(np.kron(np.eye(q), B) - np.kron(A.T, np.eye(Q)))
    M = np.vstack(blocks)
    _, s, Vh = np.linalg.svd(M)
    Tvec = Vh[-1].conj()
    gap = (s[-2] - s[-1], s[-1])
    T = Tvec.reshape((q, Q)).T  # undo column-major vec
    # row-polar normalize to a coisometry: T <- (T T*)^{-1/2} T
    G = T @ T.conj().T
    ev, U = np.linalg.eigh(G)
    ev = np.maximum(ev, 1e-30)
    T = U @ np.diag(ev ** -0.5) @ U.conj().T @ T
    res = max(np.linalg.norm(B @ T - T @ A) for A, B in pairs)
    return T, gap, res


def run(p, k):
    q, Q = p ** k, p ** (k - 2)
    wq, wQ = weil_ops(q), weil_ops(Q)
    # w diagnostics at level q
    Xq, Zq = heis(q)
    c1 = min(np.linalg.norm(wq @ Xq @ wq.conj().T - Zq),
             np.linalg.norm(wq @ Xq @ wq.conj().T - Zq.conj().T))
    w4 = wq @ wq @ wq @ wq
    w4s = np.trace(w4) / q
    w4dist = np.linalg.norm(w4 - w4s * np.eye(q)) / np.sqrt(q)
    T, (sgap, smin), res = solve_transport(q, Q, p)
    L = wQ.conj().T @ T @ wq @ T.conj().T
    sc = np.trace(L) / Q
    nonsc = np.linalg.norm(L - sc * np.eye(Q)) / np.sqrt(Q)
    print(f"p={p} k={k} (q={q}->Q={Q}): "
          f"loop scalar {sc:.6f} |.|={abs(sc):.4f} "
          f"arg/2pi={np.angle(sc) / (2 * np.pi):+.4f} "
          f"nonscalarity={nonsc:.2e}", flush=True)
    print(f"    diag: intertwine-res={res:.2e} smin={smin:.2e} "
          f"schur-gap={sgap:.2e} wXw*~Z dist={c1:.2e} "
          f"w4: scalar={w4s:.4f} dist={w4dist:.2e}", flush=True)


for (p, k) in ((3, 3), (3, 4), (5, 3)):
    run(p, k)
print("FLUX-TWO-PRIME-DONE")
