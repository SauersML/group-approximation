#!/usr/bin/env python3
"""Verification script for transpose-average-kills-positivity-only-channel-rounding.

S = (id + theta)/2 on M_d, theta = transpose.  Checks, for d = 2..6:

  (a) S is unital, trace preserving, L^2(tr)-self-adjoint and exactly idempotent;
      S is positive (random PSD inputs) and satisfies Kadison's inequality on
      random Hermitian inputs, but fails Schwarz at e_12 and is not 2-positive.
  (b) Choi spectrum of S: -1/2 with multiplicity d(d-1)/2, +1/2 with multiplicity
      d(d+1)/2 - 1, (d+1)/2 once.  Distance of C_S to the PSD cone equals
      (1/2) sqrt(d(d-1)/2), attained by the CP map with Choi matrix (C_S)_+.
  (c) Haar identity E_u ||Phi(u)||_2^2 = ||C_Phi||_HS^2 / d^2 (Monte Carlo).
  (d) For sample unital *-subalgebras A (scalars, masa, block diagonals,
      I_m (x) M_k, M_d, each conjugated by a random unitary):
      ||C_S - C_{E_A}||_HS / d >= sqrt((d-1)/(2d)), equality for A = M_d.
  (e) Exact failure of multiplicative closure: for real symmetric contractions
      a, b fixed by S, S(ab) - ab = -[a,b]/2; with a = Z(x)I, b = X(x)I (d even)
      ||S(ab) - ab||_2 = 1 although ||S^2 - S|| = 0.

Run: nice -n 10 timeout 1200 python3 transpose_obstruction.py
"""
import numpy as np

rng = np.random.default_rng(20260917)
TOL = 1e-9


def tau(x):
    return np.trace(x).real / x.shape[0]


def n2(x):
    return np.sqrt(max(tau(x.conj().T @ x), 0.0))


def S(x):
    return 0.5 * (x + x.T)


def choi(phi, d):
    C = np.zeros((d * d, d * d), dtype=complex)
    for i in range(d):
        for j in range(d):
            e = np.zeros((d, d), dtype=complex)
            e[i, j] = 1
            C += np.kron(e, phi(e))
    return C


def haar_unitary(d):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    ph = np.diag(r) / np.abs(np.diag(r))
    return q * ph


def E_blocks(U, blocks, mult):
    """Trace-preserving conditional expectation onto U (bigoplus_k I_{m_k} (x) M_{n_k}) U^*.
    blocks: list of n_k, mult: list of m_k, sum m_k n_k = d."""
    def E(x):
        y = U.conj().T @ x @ U
        out = np.zeros_like(y)
        off = 0
        for n, m in zip(blocks, mult):
            sz = n * m
            B = y[off:off + sz, off:off + sz]
            # B acts on C^m (x) C^n ; expectation onto I_m (x) M_n = partial trace over C^m / m
            B4 = B.reshape(m, n, m, n)
            red = np.einsum('ajak->jk', B4) / m
            out[off:off + sz, off:off + sz] = np.kron(np.eye(m), red)
            off += sz
        return U @ out @ U.conj().T
    return E


def check(d):
    I = np.eye(d)
    report = {}
    # (a) basic structure
    xs = [rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)) for _ in range(20)]
    assert np.allclose(S(I), I)
    for x in xs:
        assert abs(np.trace(S(x)) - np.trace(x)) < TOL
        assert np.allclose(S(S(x)), S(x))
        y = xs[0]
        assert abs(np.trace(S(x).conj().T @ y) - np.trace(x.conj().T @ S(y))) < 1e-8
        p = x @ x.conj().T
        assert np.linalg.eigvalsh(S(p)).min() > -1e-9
        h = x + x.conj().T
        assert np.linalg.eigvalsh(S(h @ h) - S(h) @ S(h)).min() > -1e-8  # Kadison
    e12 = np.zeros((d, d)); e12[0, 1] = 1
    schwarz = S(e12.T @ e12) - S(e12).T @ S(e12)
    report['schwarz_min_eig_e12'] = np.linalg.eigvalsh(schwarz).min()
    assert report['schwarz_min_eig_e12'] < -0.2
    # 2-positivity fails on the (PSD) Choi matrix of the identity on the corner M_2
    Om = np.zeros((2 * d, 2 * d))
    for i in range(2):
        for j in range(2):
            e = np.zeros((2, 2)); e[i, j] = 1
            f = np.zeros((d, d)); f[i, j] = 1
            Om += np.kron(e, f)
    SOm = np.zeros_like(Om)
    for i in range(2):
        for j in range(2):
            e = np.zeros((2, 2)); e[i, j] = 1
            f = np.zeros((d, d)); f[i, j] = 1
            SOm += np.kron(e, S(f))
    report['two_positivity_min_eig'] = np.linalg.eigvalsh(SOm).min()
    assert np.linalg.eigvalsh(Om).min() > -TOL and report['two_positivity_min_eig'] < -0.4

    # (b) Choi spectrum and distance to PSD cone
    CS = choi(S, d)
    ev = np.sort(np.linalg.eigvalsh(CS))
    expect = np.sort([-0.5] * (d * (d - 1) // 2) + [0.5] * (d * (d + 1) // 2 - 1) + [(d + 1) / 2])
    assert np.allclose(ev, expect)
    w, V = np.linalg.eigh(CS)
    Cplus = (V * np.clip(w, 0, None)) @ V.conj().T
    dist_cp = np.linalg.norm(CS - Cplus)
    assert abs(dist_cp - 0.5 * np.sqrt(d * (d - 1) / 2)) < 1e-9
    report['cp_lower_bound'] = dist_cp / d
    assert abs(report['cp_lower_bound'] - np.sqrt((d - 1) / (8 * d))) < 1e-12

    # (c) Haar identity for Phi = S - id
    phi = lambda x: S(x) - x
    Cphi = choi(phi, d)
    mc = np.mean([n2(phi(haar_unitary(d))) ** 2 for _ in range(4000)])
    report['haar_mc'] = mc
    report['haar_exact'] = np.linalg.norm(Cphi) ** 2 / d ** 2
    assert abs(mc - report['haar_exact']) < 0.05

    # (d) algebra lower bound
    lb = np.sqrt((d - 1) / (2 * d))
    algebras = {'scalars': ([1], [d]), 'masa': ([1] * d, [1] * d), 'M_d': ([d], [1])}
    if d >= 3:
        algebras['M_2+M_(d-2)'] = ([2, d - 2], [1, 1])
    if d % 2 == 0:
        algebras['I_2(x)M_(d/2)'] = ([d // 2], [2])
        algebras['M_2(x)I_(d/2)'] = ([2], [d // 2])
    dists = {}
    for name, (blocks, mult) in algebras.items():
        for trial in range(3):
            U = haar_unitary(d) if trial else np.eye(d)
            E = E_blocks(U, blocks, mult)
            # sanity: E idempotent, unital
            x = xs[1]
            assert np.allclose(E(E(x)), E(x)) and np.allclose(E(I), I)
            CA = choi(E, d)
            assert np.linalg.eigvalsh(CA).min() > -1e-9
            val = np.linalg.norm(CS - CA) / d
            assert val >= lb - 1e-9, (name, val, lb)
            dists[name] = min(dists.get(name, 9), val)
    report['algebra_min_haar_distance'] = dists
    report['bound_sqrt((d-1)/2d)'] = lb
    assert abs(dists['M_d'] - lb) < 1e-9

    # (e) multiplicative closure failure
    if d % 2 == 0:
        Z = np.diag([1.0, -1.0]); X = np.array([[0.0, 1.0], [1.0, 0.0]])
        a = np.kron(Z, np.eye(d // 2)); b = np.kron(X, np.eye(d // 2))
        assert np.allclose(S(a), a) and np.allclose(S(b), b)
        report['mult_defect'] = n2(S(a @ b) - a @ b)
        assert abs(report['mult_defect'] - 1) < 1e-12
    else:
        Z = np.diag([1.0, -1.0]); X = np.array([[0.0, 1.0], [1.0, 0.0]])
        a = np.zeros((d, d)); b = np.zeros((d, d))
        a[:2, :2] = Z; b[:2, :2] = X
        report['mult_defect'] = n2(S(a @ b) - a @ b)
        assert abs(report['mult_defect'] - np.sqrt(2 / d)) < 1e-12
    # random real symmetric: S(ab)-ab = -[a,b]/2
    for _ in range(10):
        a = rng.standard_normal((d, d)); a = a + a.T
        b = rng.standard_normal((d, d)); b = b + b.T
        assert np.allclose(S(a @ b) - a @ b, -(a @ b - b @ a) / 2)
    return report


if __name__ == '__main__':
    for d in range(2, 7):
        r = check(d)
        print(f"d={d}:")
        for k, v in r.items():
            if isinstance(v, dict):
                print(f"   {k}: " + ", ".join(f"{n}={x:.6f}" for n, x in v.items()))
            else:
                print(f"   {k}: {v:.6f}")
    print("ALL CHECKS PASSED")
