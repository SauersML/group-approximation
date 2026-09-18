"""Independent referee search for (SR*) (lane ref-04, 2026-09-17).

Written from scratch; shares no code with the other scripts in this folder.

(SR*): for K = sum_P beta_P P (P non-identity Hermitian Paulis), W = sum|beta_P|,
lambda = lambda_max(K):  stab(K) >= lambda - (1/sqrt2)(W - lambda).
We maximize ratio(K) = (lambda - stab)/(W - lambda) and look for ratio > 1/sqrt2.

Stabilizer states are enumerated exactly by breadth-first closure of |0...0>
under H, S and CNOT, deduplicated up to global phase
(expected counts 6, 60, 1080, 36720 for n = 1..4).

usage: python3 referee_ref04_search.py n random_trials opt_restarts seed
"""
import itertools
import sys
import numpy as np
from scipy.optimize import minimize

C = 1 / np.sqrt(2)
I2 = np.eye(2, dtype=complex)
PX = np.array([[0, 1], [1, 0]], dtype=complex)
PY = np.array([[0, -1j], [1j, 0]], dtype=complex)
PZ = np.array([[1, 0], [0, -1]], dtype=complex)
SINGLE = [I2, PX, PY, PZ]


def kron_all(ms):
    out = np.array([[1]], dtype=complex)
    for m in ms:
        out = np.kron(out, m)
    return out


def paulis(n):
    labels = list(itertools.product(range(4), repeat=n))[1:]  # drop identity
    mats = np.array([kron_all([SINGLE[i] for i in lab]) for lab in labels])
    return labels, mats


def gate_1q(g, q, n):
    return kron_all([g if k == q else I2 for k in range(n)])


def cnot(c, t, n):
    d = 2 ** n
    U = np.zeros((d, d), dtype=complex)
    for b in range(d):
        bits = [(b >> (n - 1 - k)) & 1 for k in range(n)]
        if bits[c]:
            bits[t] ^= 1
        b2 = sum(bit << (n - 1 - k) for k, bit in enumerate(bits))
        U[b2, b] = 1
    return U


def key(v):
    i = np.argmax(np.abs(v) > 1e-9)
    v = v * np.conj(v[i]) / abs(v[i])
    return tuple((np.round(np.concatenate([v.real, v.imag]), 6) + 0.0).tolist())


def stabilizer_states(n):
    H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
    S = np.diag([1, 1j])
    gates = [gate_1q(H, q, n) for q in range(n)] + [gate_1q(S, q, n) for q in range(n)]
    gates += [cnot(a, b, n) for a in range(n) for b in range(n) if a != b]
    v0 = np.zeros(2 ** n, dtype=complex)
    v0[0] = 1
    seen = {key(v0): v0}
    frontier = [v0]
    while frontier:
        nxt = []
        for v in frontier:
            for g in gates:
                w = g @ v
                k = key(w)
                if k not in seen:
                    seen[k] = w
                    nxt.append(w)
        frontier = nxt
    return np.array(list(seen.values()))


def expectation_table(states, mats):
    # E[s, P] = <phi_s|P|phi_s>, entries in {0, +-1}
    E = np.stack([np.sum(states.conj() * (states @ P.T), axis=1).real for P in mats], axis=1)
    assert np.allclose(E, np.round(E), atol=1e-8)
    return np.round(E)


def ratio(beta, E, mats):
    K = np.tensordot(beta, mats, axes=1)
    lam = np.linalg.eigvalsh(K)[-1]
    W = np.abs(beta).sum()
    stab = (E @ beta).max()
    den = W - lam
    if den < 1e-9 * max(W, 1e-12):
        return 0.0, lam, stab, W
    return (lam - stab) / den, lam, stab, W


def main():
    n = int(sys.argv[1])
    trials = int(sys.argv[2])
    restarts = int(sys.argv[3])
    seed = int(sys.argv[4])
    rng = np.random.default_rng(seed)
    labels, mats = paulis(n)
    states = stabilizer_states(n)
    print(f"n={n}: {len(states)} stabilizer states, {len(labels)} Paulis", flush=True)
    E = expectation_table(states, mats)
    m = len(labels)
    best = (-1, None)

    def consider(beta, tag):
        nonlocal best
        r, lam, stab, W = ratio(beta, E, mats)
        # direct (SR*) slack, normalized by W
        slack = (stab - (lam - C * (W - lam))) / max(W, 1e-12)
        if slack < -1e-9:
            print(f"VIOLATION {tag}: ratio={r:.10f} beta={beta.tolist()}", flush=True)
        if r > best[0]:
            best = (r, beta.copy())

    # 1. random sums: dense Gaussian, sparse supports, +-1 coefficients
    for tr in range(trials):
        kind = tr % 3
        if kind == 0:
            beta = rng.standard_normal(m)
        elif kind == 1:
            k = rng.integers(2, min(m, 8) + 1)
            beta = np.zeros(m)
            beta[rng.choice(m, k, replace=False)] = rng.standard_normal(k)
        else:
            k = rng.integers(2, min(m, 10) + 1)
            beta = np.zeros(m)
            beta[rng.choice(m, k, replace=False)] = rng.choice([-1.0, 1.0], k)
        consider(beta, f"random{tr}")
    print(f"after random: best ratio {best[0]:.10f}", flush=True)

    # 2. adversarial: states' Pauli vectors raised to powers (magic-type)
    Tst = np.array([np.cos(np.pi / 8), np.sin(np.pi / 8)], dtype=complex)
    Fst = np.array([np.sqrt((1 + 1 / np.sqrt(3)) / 2),
                    np.exp(1j * np.pi / 4) * np.sqrt((1 - 1 / np.sqrt(3)) / 2)])
    specials = {"T^n": kron_all([Tst.reshape(2, 1)] * n).ravel(),
                "F^n": kron_all([Fst.reshape(2, 1)] * n).ravel()}
    for j in range(20):
        v = rng.standard_normal(2 ** n) + 1j * rng.standard_normal(2 ** n)
        specials[f"haar{j}"] = v / np.linalg.norm(v)
    for name, psi in specials.items():
        x = np.einsum('i,pij,j->p', psi.conj(), mats, psi).real
        for p in [0.5, 1, 2, 3, 6, 12]:
            beta = np.sign(x) * np.abs(x) ** p
            beta[np.abs(x) < 1e-12] = 0
            consider(beta, f"{name}^p={p}")
    print(f"after magic families: best ratio {best[0]:.10f}", flush=True)

    # 3. local optimization of the ratio (Nelder-Mead on sparse supports + Powell dense)
    for rs in range(restarts):
        k = int(rng.integers(2, min(m, 7) + 1))
        supp = rng.choice(m, k, replace=False)

        def f(y, supp=supp):
            beta = np.zeros(m)
            beta[supp] = y
            return -ratio(beta, E, mats)[0]

        y0 = rng.standard_normal(k)
        res = minimize(f, y0, method='Nelder-Mead',
                       options={'maxiter': 3000, 'xatol': 1e-10, 'fatol': 1e-12})
        beta = np.zeros(m)
        beta[supp] = res.x
        consider(beta, f"opt{rs}")
    print(f"after optimization: best ratio {best[0]:.10f}", flush=True)
    b = best[1]
    nz = [(labels[i], round(float(b[i]), 4)) for i in np.nonzero(np.abs(b) > 1e-6 * np.abs(b).max())[0]]
    print("best support:", nz[:12], flush=True)
    print(f"FINAL n={n} max ratio {best[0]:.10f} (1/sqrt2 = {C:.10f})")


if __name__ == "__main__":
    main()
