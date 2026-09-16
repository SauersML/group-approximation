"""Numerical sanity check for the delocalized Bott invariant (swarm note 2026-09-16).

Toy group G = (Z^2 x Z/3) x| Z/2, r u r = u, r v r = v^-1, r w r = w^-1.
Model on C^n + C^n: u -> U+U, v -> V+V*, w -> omega I + conj(omega) I, r -> swap,
with (U, V) the clock-shift pair.  Checks:
  * relator defects of the model (only [u,v] is inexact, defect |1 - e^{2 pi i/n}|);
  * beta_omega = Bott of the compressions to the omega-eigenspace of phi(w) is +1,
    beta_conj = -1, and the total Bott index is 0;
  * Bott is computed as (1/2 pi i) Tr log(V U V* U*) with the principal branch.
Also checks the SL_4 centralizer facts used in section 5 over a symbolic Laurent ring
(sympy, t a symbol): g = diag(a, a^-1, 1, 1), s1 = diag(t,1,1/t,1), s2 = diag(1,t,1,1/t),
the permutation matrix w' of (12)(34) has det 1, w' g w'^-1 = g^-1, w' s1 w'^-1 = s2.
"""
import numpy as np
import sympy as sp


def clock_shift(n):
    U = np.diag(np.exp(2j * np.pi * np.arange(n) / n))
    V = np.roll(np.eye(n), 1, axis=0)
    return U, V


def bott(u, v):
    w = v @ u @ v.conj().T @ u.conj().T
    ev = np.linalg.eigvals(w)
    return float(np.real(np.sum(np.log(ev)) / (2j * np.pi)))


def model(n):
    U, V = clock_shift(n)
    Z = np.zeros((n, n))
    I = np.eye(n)
    om = np.exp(2j * np.pi / 3)
    blk = lambda A, B: np.block([[A, Z], [Z, B]])
    u = blk(U, U)
    v = blk(V, V.conj().T)
    w = blk(om * I, np.conj(om) * I)
    r = np.block([[Z, I], [I, Z]])
    return u, v, w, r


def defects(u, v, w, r):
    nrm = lambda X: np.linalg.norm(X, 2)
    inv = lambda X: X.conj().T
    return {
        "[u,v]": nrm(u @ v - v @ u),
        "[u,w]": nrm(u @ w - w @ u),
        "[v,w]": nrm(v @ w - w @ v),
        "w^3-1": nrm(w @ w @ w - np.eye(len(w))),
        "r^2-1": nrm(r @ r - np.eye(len(r))),
        "rur-u": nrm(r @ u @ r - u),
        "rvr-v^-1": nrm(r @ v @ r - inv(v)),
        "rwr-w^-1": nrm(r @ w @ r - inv(w)),
    }


def compress_bott(u, v, w, omega):
    ev, P = np.linalg.eig(w)
    idx = np.where(np.abs(ev - omega) < 0.5)[0]
    Q = np.linalg.qr(P[:, idx])[0]
    cu = Q.conj().T @ u @ Q
    cv = Q.conj().T @ v @ Q
    return bott(cu, cv)


if __name__ == "__main__":
    om = np.exp(2j * np.pi / 3)
    for n in (8, 16, 48):
        u, v, w, r = model(n)
        d = defects(u, v, w, r)
        print(f"n={n} defects:", {k: round(x, 6) for k, x in d.items()})
        print("  beta_omega =", round(compress_bott(u, v, w, om), 6),
              " beta_conj =", round(compress_bott(u, v, w, np.conj(om)), 6),
              " total Bott =", round(bott(u, v), 6))
    t, a = sp.symbols("t a", nonzero=True)
    g = sp.diag(a, 1 / a, 1, 1)
    s1 = sp.diag(t, 1, 1 / t, 1)
    s2 = sp.diag(1, t, 1, 1 / t)
    wp = sp.Matrix([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])
    print("det w' =", wp.det())
    print("s1, s2 in SL_4 and commute with g:", s1.det() == 1, s2.det() == 1,
          sp.simplify(s1 * g - g * s1) == sp.zeros(4), sp.simplify(s2 * g - g * s2) == sp.zeros(4))
    print("w' g w'^-1 == g^-1:", sp.simplify(wp * g * wp.inv() - g.inv()) == sp.zeros(4))
    print("w' s1 w'^-1 == s2:", sp.simplify(wp * s1 * wp.inv() - s2) == sp.zeros(4))
