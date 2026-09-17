#!/usr/bin/env python3
"""Clifford long codes in the binary folded long-code noise test.

Checks, exactly and on small instances, the three statements of
research/clifford-long-codes-realize-pairing-value-in-binary-noise-test.md:

 (C1) gamma(w) = sum_i w_i gamma_i with anticommuting Hermitian unitaries
      gamma_i is a Hermitian unitary when |w| = 1, and tau(gamma(w) gamma(w'))
      = <w, w'>.  Hence F_u(X) = gamma(sum_x (-1)^{X_x} w_{u,x}) is a folded
      +-1 observable whenever the w_{u,x} are orthogonal with total mass 1.
 (C2) With Alice measuring F_u(X) and Bob measuring conj(F_v(Y)) on the
      maximally entangled state, the acceptance probability of the binary
      test R_(rho,2)(Psi) equals
          1/2 + (rho^3 / 2) E_b sum_j | E_{u|b} W_{u,b,j} |^2,
      W_{u,b,j} = sum_{x in pi_{u,b}^{-1}(j)} w_{u,x}.
      Checked both through the trace formula and through an explicit
      kron-product quantum strategy on the maximally entangled state.
 (C3) For the right-merged game Psi(U) of a unique game U and SDP-1
      (Kempe--Regev--Toner) vectors u_{u,a}, v_{v,b} with nonnegative cross
      inner products, taking w = u gives
          E_b sum_j |E_u W|^2 >= (E_{uv} sum_a <u_{u,a}, v_{v,phi_uv(a)}>)^2.

It also reports the best classical folded labeling of the tiny output game
against the Clifford strategy (an anomaly scan, not part of any claim).

Run: python3 clifford_noise_test.py   (numpy only; about 70 s)
"""
import itertools
import numpy as np

rng = np.random.default_rng(20260917)

# ---------- Clifford generators (Jordan--Wigner) ----------
I2 = np.eye(2)
PX = np.array([[0, 1], [1, 0]], dtype=complex)
PY = np.array([[0, -1j], [1j, 0]], dtype=complex)
PZ = np.array([[1, 0], [0, -1]], dtype=complex)


def kron_all(ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out


def clifford(D):
    q = (D + 1) // 2
    gens = []
    for i in range(q):
        for P in (PX, PY):
            gens.append(kron_all([PZ] * i + [P] + [I2] * (q - i - 1)))
    return gens[:D]


def gamma(gens, w):
    return sum(wi * g for wi, g in zip(w, gens))


def tau(M):
    return (np.trace(M) / M.shape[0]).real


# ---------- instance: unique game U, right merge Psi(U) ----------
K2 = 4                      # left alphabet 2k
K = 2                       # right alphabet k
NL, NR = 2, 2               # left / right vertices of U
phi = {(u, v): rng.permutation(K2) for u in range(NL) for v in range(NR)}
sigmas = []                 # all 2-to-1 maps [4] -> [2]
for S in itertools.combinations(range(K2), 2):
    sig = np.ones(K2, dtype=int)
    sig[list(S)] = 0
    sigmas.append(sig)
# Psi(U): right vertex (v, sigma); edge (u,(v,sigma)) carries pi = sigma o phi_uv
RIGHT = [(v, s) for v in range(NR) for s in range(len(sigmas))]


def pi(u, b):
    v, s = b
    return sigmas[s][phi[(u, v)]]


rho = 0.9
ALL_X = [np.array(bits) for bits in itertools.product((0, 1), repeat=K2)]


def xindex(X):
    return int(''.join(str(int(t)) for t in X), 2)

ALL_A = [np.array(bits) for bits in itertools.product((0, 1), repeat=K)]


def kern(s, t):
    return rho * (s == t) + (1 - rho) / 2


def joint_XY(u, v, b):
    """exact law p[X,Y] of the test's two queries on edge pair (u,b),(v,b)"""
    p = np.zeros((len(ALL_X), len(ALL_X)))
    pu, pv = pi(u, b), pi(v, b)
    for A in ALL_A:
        for B in ALL_A:
            pAB = (1 / 2 ** K) * np.prod([kern(A[j], B[j]) for j in range(K)])
            P, Q = A[pu], B[pv]
            px = np.array([np.prod([kern(P[x], X[x]) for x in range(K2)]) for X in ALL_X])
            qy = np.array([np.prod([kern(Q[y], Y[y]) for y in range(K2)]) for Y in ALL_X])
            p += pAB * np.outer(px, qy)
    return p


JOINT = {(u, v, b): joint_XY(u, v, b) for u in range(NL) for v in range(NL) for b in RIGHT}


def orth_frame(D, nonneg_disjoint=False):
    """K2 orthogonal vectors in R^D of total squared mass 1"""
    if nonneg_disjoint:
        perm = rng.permutation(D)
        chunks = np.array_split(perm, K2)
        W = np.zeros((K2, D))
        for x, c in enumerate(chunks):
            W[x, c] = rng.random(len(c))
    else:
        Q, _ = np.linalg.qr(rng.standard_normal((D, D)))
        W = Q[:K2].copy()
    mass = rng.random(K2) + 0.05
    for x in range(K2):
        W[x] *= np.sqrt(mass[x] / mass.sum()) / np.linalg.norm(W[x])
    return W


def acceptance_trace(gens, frames):
    F = {(u, i): gamma(gens, ((-1.0) ** X) @ frames[u]) for u in range(NL) for i, X in enumerate(ALL_X)}
    for M in F.values():
        assert np.allclose(M, M.conj().T) and np.allclose(M @ M, np.eye(M.shape[0]))
    for u in range(NL):
        for i, X in enumerate(ALL_X):
            j = xindex(1 - X)
            assert np.allclose(F[(u, j)], -F[(u, i)])          # folded
    tot = 0.0
    for b in RIGHT:
        for u in range(NL):
            for v in range(NL):
                G = np.array([[tau(F[(u, i)] @ F[(v, k)]) for k in range(len(ALL_X))] for i in range(len(ALL_X))])
                tot += (JOINT[(u, v, b)] * (1 + G) / 2).sum()
    return tot / (len(RIGHT) * NL * NL), F


def acceptance_kron(F, trials=6):
    """explicit two-prover strategy on the maximally entangled state"""
    d = F[(0, 0)].shape[0]
    psi = np.eye(d).reshape(d * d) / np.sqrt(d)
    tot = 0.0
    for b in RIGHT[:trials]:
        for u in range(NL):
            for v in range(NL):
                p = JOINT[(u, v, b)]
                acc = np.zeros_like(p)
                for i in range(len(ALL_X)):
                    for k in range(len(ALL_X)):
                        if p[i, k] < 1e-12:
                            continue
                        Pa = [(np.eye(d) + s * F[(u, i)]) / 2 for s in (1, -1)]
                        Pb = [(np.eye(d) + s * F[(v, k)].conj()) / 2 for s in (1, -1)]
                        acc[i, k] = sum((psi.conj() @ np.kron(Pa[s], Pb[s]) @ psi).real for s in (0, 1))
                tot += (p * acc).sum()
    return tot / (trials * NL * NL)


def pairing_value(frames):
    tot = 0.0
    for b in RIGHT:
        for j in range(K):
            Wbar = np.mean([frames[u][pi(u, b) == j].sum(axis=0) for u in range(NL)], axis=0)
            tot += Wbar @ Wbar
    return tot / len(RIGHT)


def check_identity(D, nonneg):
    gens = clifford(D)
    for i, g in enumerate(gens):
        for k, h in enumerate(gens):
            assert np.allclose(g @ h + h @ g, 2 * (i == k) * np.eye(g.shape[0]))
    frames = [orth_frame(D, nonneg) for _ in range(NL)]
    acc, F = acceptance_trace(gens, frames)
    formula = 0.5 + rho ** 3 / 2 * pairing_value(frames)
    return acc, formula, F, frames


def classical_best():
    """best classical folded labeling of R_(rho,2)(Psi(U))"""
    half = [i for i, X in enumerate(ALL_X) if X[0] == 0]
    idx_neg = {i: xindex(1 - ALL_X[i]) for i in half}
    n = len(half)
    # correlation kernel C[(u,i),(v,k)] = E accept-contrib of f_u(X_i) f_v(Y_k)
    C = np.zeros((NL * len(ALL_X), NL * len(ALL_X)))
    for b in RIGHT:
        for u in range(NL):
            for v in range(NL):
                C[u * 16:(u + 1) * 16, v * 16:(v + 1) * 16] += JOINT[(u, v, b)]
    C /= len(RIGHT) * NL * NL
    # fold: f(X_neg) = -f(X)
    T = np.zeros((NL * 16, NL * n))
    for u in range(NL):
        for c, i in enumerate(half):
            T[u * 16 + i, u * n + c] = 1
            T[u * 16 + idx_neg[i], u * n + c] = -1
    M = T.T @ C @ T
    best = -1
    for bits in itertools.product((1, -1), repeat=NL * n - 1):
        f = np.array((1,) + bits, dtype=float)
        best = max(best, f @ M @ f)
    return 0.5 + best / 2


def check_merge_bound(D):
    frames_u = [orth_frame(D, True) for _ in range(NL)]
    # right SDP-1 vectors: nonnegative, disjoint supports -> orthogonal, <u,v> >= 0
    frames_v = [orth_frame(D, True) for _ in range(NR)]
    s = np.mean([sum(frames_u[u][a] @ frames_v[v][phi[(u, v)][a]] for a in range(K2))
                 for u in range(NL) for v in range(NR)])
    # SDP-1 also needs sum_a u_a = z = sum_b v_b; we only use orthogonality,
    # unit total mass and nonnegativity, which is all the proof uses.
    return pairing_value(frames_u), s ** 2


if __name__ == "__main__":
    for D, nonneg in ((6, False), (8, False), (8, True)):
        acc, formula, F, frames = check_identity(D, nonneg)
        print(f"C1/C2 D={D} nonneg={nonneg}: trace acceptance {acc:.12f}  formula {formula:.12f}")
        assert abs(acc - formula) < 1e-10
    acc, formula, F, frames = check_identity(6, False)
    kr = acceptance_kron(F)
    # the kron check covers the first 6 right vertices; recompute formula restricted
    part = 0.0
    for b in RIGHT[:6]:
        for u in range(NL):
            for v in range(NL):
                G = np.array([[tau(F[(u, i)] @ F[(v, k)]) for k in range(16)] for i in range(16)])
                part += (JOINT[(u, v, b)] * (1 + G) / 2).sum()
    part /= 6 * NL * NL
    print(f"C2 explicit maximally-entangled strategy (6 right vertices): {kr:.12f} vs trace {part:.12f}")
    assert abs(kr - part) < 1e-10
    for t in range(20):
        lhs, rhs = check_merge_bound(8)
        assert lhs >= rhs - 1e-12, (lhs, rhs)
    print("C3 merge bound E_b sum_j |E_u W|^2 >= s^2 held on 20 random nonnegative frames")
    cb = classical_best()
    best_q = max(check_identity(8, False)[0] for _ in range(30))
    print(f"anomaly scan: best classical folded value {cb:.6f}; best of 30 random Clifford frames {best_q:.6f}")
    print("ALL CHECKS PASSED")
