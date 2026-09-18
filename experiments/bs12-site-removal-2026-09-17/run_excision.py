"""Numerical check of the run-excision construction in
research/bs12-identity-padding-is-removable-in-operator-norm-proof.md.

For a cyclic binary word w (both digits present) build the exact BS(1,2) packet
    Z e_j = exp(2 pi i theta_j) e_j,  C e_j = e_{j-1}  (weight mu on one depth-1 edge),
theta_j = reading of w from position j.  For parameters r, s excise, in every run of
length z >= s+4r+1, the segment [d+r, d+z-s-r) as a b-trivial cycle, gauged over the 2r
pairs (c+i, c+p+i).  Report:
  exactness of (C1, Z1), ||C1-C|| vs pi/(2r-1), ||Z1-Z|| vs 3 pi 2^-s,
  max over low eigenvectors y of h of ||(1-P_F1) y||^2 / E(y) vs a = 4^(s+2r-1)+(2r+1)^2,
and an end-to-end padding removal: V = span of the k lowest eigenvectors of h.
"""
import numpy as np
from scipy.linalg import expm, polar, null_space
import sys


def readings(w):
    L = len(w)
    den = 2 ** L - 1
    return np.array([int("".join(map(str, w[j:] + w[:j])), 2) / den for j in range(L)])


def runs(w):
    """list of (d, z): run occupies positions d..d+z-1 (cyclic)."""
    L = len(w)
    starts = [j for j in range(L) if w[j] != w[j - 1]]
    out = []
    for a, d in enumerate(starts):
        nxt = starts[(a + 1) % len(starts)]
        out.append((d, (nxt - d) % L or L))
    return out


def packet(w, mu):
    L = len(w)
    th = readings(w)
    Z = np.diag(np.exp(2j * np.pi * th))
    C = np.zeros((L, L), complex)
    jstar = [(d + z - 1) % L for d, z in runs(w)][0]      # a depth-1 site
    for j in range(L):
        C[(j - 1) % L, j] = mu if j == jstar else 1
    return C, Z, jstar


def excise(w, mu, r, s):
    L = len(w)
    C, Z, jstar = packet(w, mu)
    long_runs = [(d, z) for d, z in runs(w) if z >= s + 4 * r + 1]
    deleted, pairs, segs = set(), [], []
    for d, z in long_runs:
        p = z - s - 2 * r
        c = d + r
        seg = [(c + t) % L for t in range(p)]
        segs.append(seg)
        deleted |= set(seg)
        pairs.append([((c + i) % L, (c + p + i) % L) for i in range(-r, r)])
    rest = [j for j in range(L) if j not in deleted]
    wnew = [w[j] for j in rest]
    thn = readings(wnew) if len(set(wnew)) > 1 else np.zeros(len(wnew))
    lam1 = np.ones(L, complex)
    for a, j in enumerate(rest):
        lam1[j] = np.exp(2j * np.pi * thn[a])
    Zp = np.diag(lam1)
    Cp = np.zeros((L, L), complex)
    for a, j in enumerate(rest):
        Cp[rest[a - 1], j] = mu if j == jstar else 1
    for seg in segs:
        p = len(seg)
        for t in range(p):
            Cp[seg[t - 1], seg[t]] = 1          # seg[0] -> seg[p-1]
    # gauge
    sig = np.array([[0, 1], [1, 0]], complex)
    Pm = (np.eye(2) - sig) / 2
    Wm = np.eye(L, dtype=complex)
    ginfo = []
    for pr in pairs:
        u = expm(1j * np.pi * Pm / (2 * r - 1))
        g = np.eye(2, dtype=complex)
        gs = [g]
        for i in range(-r + 1, r):
            ci = sig if i == 0 else np.eye(2)
            g = ci.conj().T @ g @ u
            gs.append(g)
        ginfo.append(np.linalg.norm(gs[-1] - np.eye(2)))
        for (a, b), g in zip(pr, gs):
            idx = [a, b]
            Wm[np.ix_(idx, idx)] = g
    C1 = Wm.conj().T @ Cp @ Wm
    Z1 = Wm.conj().T @ Zp @ Wm
    return C, Z, C1, Z1, len(long_runs), max(ginfo, default=0.0)


def opn(M):
    return np.linalg.norm(M, 2)


def remove_padding(C, Z, C1, Z1, V):
    """V: orthonormal columns.  Returns exact packet on V^perp (in an orthonormal
    basis Q of V^perp) and the reference compressions A, B."""
    K = C.shape[0]
    F1 = null_space(Z1 - np.eye(K), rcond=1e-9)
    PF = F1 @ F1.conj().T
    theta = opn((np.eye(K) - PF) @ V)
    if theta >= 0.5:
        # outside the regime of the theorem (sqrt(2a) eps < 1/2 fails): V is not
        # close to the new fixed space, so there is nothing to split off
        return dict(theta=theta, skipped=True)
    V1, _ = np.linalg.qr(PF @ V)
    P, Q = V @ V.conj().T, V1 @ V1.conj().T
    # U2: make V1 reducing and trivial inside F1
    Qc = PF - Q
    blk = Qc @ C1 @ Qc
    # polar part of blk on range(Qc)
    B1 = null_space(np.eye(K) - Qc, rcond=1e-9)          # basis of range Qc
    if B1.shape[1]:
        u, _ = polar(B1.conj().T @ blk @ B1)
        U2 = B1 @ u @ B1.conj().T + Q
    else:
        U2 = Q
    C2 = (np.eye(K) - PF) @ C1 @ (np.eye(K) - PF) + U2
    X = P @ Q + (np.eye(K) - P) @ (np.eye(K) - Q)
    Om, _ = polar(X)
    C3, Z3 = Om @ C2 @ Om.conj().T, Om @ Z1 @ Om.conj().T
    Qp = null_space(V.conj().T)                           # basis of V^perp
    C0, Z0 = Qp.conj().T @ C3 @ Qp, Qp.conj().T @ Z3 @ Qp
    A, _ = polar(Qp.conj().T @ C @ Qp)
    B, _ = polar(Qp.conj().T @ Z @ Qp)
    Apad = Qp @ A @ Qp.conj().T + P
    Bpad = Qp @ B @ Qp.conj().T + P
    eps = max(opn(C - Apad), opn(Z - Bpad))
    return dict(theta=theta, skipped=False, eps=eps, err_C=opn(C0 - A), err_Z=opn(Z0 - B),
                exact=opn(C0 @ Z0 @ C0.conj().T - Z0 @ Z0),
                unit=max(opn(C0 @ C0.conj().T - np.eye(len(C0))), opn(Z0 @ Z0.conj().T - np.eye(len(Z0)))),
                leak=opn(V.conj().T @ C3 @ Qp) + opn(V.conj().T @ Z3 @ Qp))


def main(word, mu, r, s, k):
    w = [int(ch) for ch in word]
    C, Z, C1, Z1, nlong, gret = excise(w, mu, r, s)
    L = len(w)
    print(f"L={L} runs={runs(w)} r={r} s={s} long_runs={nlong} gauge_return={gret:.1e}")
    print(f"  exact(C1,Z1)={opn(C1 @ Z1 @ C1.conj().T - Z1 @ Z1):.1e}"
          f"  ||C1-C||={opn(C1 - C):.4f} (bound {np.pi / (2 * r - 1):.4f})"
          f"  ||Z1-Z||={opn(Z1 - Z):.2e} (bound {3 * np.pi * 2.0 ** -s:.2e})")
    I = np.eye(L)
    h = (C - I).conj().T @ (C - I) + (Z - I).conj().T @ (Z - I)
    ev, U = np.linalg.eigh(h)
    F1 = null_space(Z1 - I, rcond=1e-9)
    PF = F1 @ F1.conj().T
    a = 4.0 ** (s + 2 * r - 1) + (2 * r + 1) ** 2
    ratios = [np.linalg.norm((I - PF) @ U[:, t]) ** 2 / ev[t] for t in range(min(6, L))]
    print(f"  lowest h eigenvalues {np.round(ev[:4], 6)}  max leak/E={max(ratios):.3g}  (a={a:.3g})")
    V = U[:, :k]
    res = remove_padding(C, Z, C1, Z1, V)
    if res["skipped"]:
        print("  padding removal k=%d: theta=||(1-P_F1)P_V||=%.3f >= 1/2, outside the theorem's regime; skipped"
              % (k, res["theta"]))
        return
    print("  theta=||(1-P_F1)P_V||=%.2e" % res["theta"])
    print("  padding removal k=%d: eps=%.4f -> errC=%.4f errZ=%.4f exact=%.1e unit=%.1e leak=%.1e"
          % (k, res["eps"], res["err_C"], res["err_Z"], res["exact"], res["unit"], res["leak"]))


if __name__ == "__main__":
    word, mu, r, s, k = sys.argv[1], complex(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    main(word, mu, r, s, k)
