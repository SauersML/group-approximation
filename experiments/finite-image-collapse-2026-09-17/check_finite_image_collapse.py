#!/usr/bin/env python3
"""Sanity check for finite-image-higman-models-collapse-opnorm.

(FIC-D): for Higman tuples u_0..u_3 generating a FINITE subgroup of U(k),
    D(u) = max_i ||u_i u_{i+1} u_i^* - u_{i+1}^2||  >=  min(1/2, max_i ||u_i - 1||).

We sample tuples from three finite groups and also run a greedy local search
that tries to minimize D - min(1/2, max_i ||u_i-1||) inside each group:
  * monomial group (q-th roots of unity times permutations), dimension n;
  * HOC-type clocks: D e_x = w^x e_x, P e_x = e_{x/2} over Z/q, conjugated by
    random monomial matchers H, packets U_j = H^j D H^-j and conjugators
    C_j = H^j P H^-j (the conjugators generate a finite group);
  * the Clifford/Weil group over Z/p (Fourier, chirp, clock, shift, dilation).
The theorem predicts that the printed minimum margin is >= 0 (up to 1e-9).
No output is a proof; the proof is in the research file.
"""
import numpy as np

rng = np.random.default_rng(20260919)


def opn(a):
    return np.linalg.norm(a, 2)


def defect(us):
    return max(opn(us[i] @ us[(i + 1) % 4] @ us[i].conj().T
                   - us[(i + 1) % 4] @ us[(i + 1) % 4]) for i in range(4))


def dist(us):
    return max(opn(u - np.eye(u.shape[0])) for u in us)


def margin(us):
    return defect(us) - min(0.5, dist(us))


def monomial(n, q):
    perm = rng.permutation(n)
    ph = np.exp(2j * np.pi * rng.integers(0, q, n) / q)
    m = np.zeros((n, n), complex)
    m[perm, np.arange(n)] = ph
    return m


def near_identity_monomial(n, q, moves=1):
    # identity with a few phases and one transposition: small-group-move proposal
    m = np.eye(n, dtype=complex)
    for _ in range(moves):
        x = rng.integers(n)
        m[x, x] = np.exp(2j * np.pi * rng.integers(0, q) / q)
    if rng.random() < 0.5:
        a, b = rng.choice(n, 2, replace=False)
        m[[a, b]] = m[[b, a]]
    return m


def clifford_gens(p):
    w = np.exp(2j * np.pi / p)
    x = np.arange(p)
    F = np.exp(2j * np.pi * np.outer(x, x) / p) / np.sqrt(p)
    Zc = np.diag(w ** x)
    X = np.roll(np.eye(p), 1, axis=0)
    inv2 = pow(2, -1, p)
    chirp = np.diag(w ** ((x * x * inv2) % p))
    dil = np.zeros((p, p))
    dil[(2 * x) % p, x] = 1
    return [F, Zc, X, chirp, dil, F.conj().T, Zc.conj().T, X.T,
            chirp.conj().T, dil.T]


def random_word(gens, length):
    m = np.eye(gens[0].shape[0], dtype=complex)
    for _ in range(length):
        m = gens[rng.integers(len(gens))] @ m
    return m


def local_search(us, propose, steps=300):
    best = margin(us)
    for _ in range(steps):
        i = rng.integers(4)
        g = propose()
        cand = list(us)
        cand[i] = g @ us[i] if rng.random() < 0.5 else us[i] @ g
        mc = margin(cand)
        if mc < best:
            us, best = cand, mc
    return best, us


def main():
    worst = np.inf
    # monomial family
    for n, q in [(3, 3), (4, 4), (5, 7), (7, 9), (9, 27)]:
        for _ in range(40):
            us = [monomial(n, q) for _ in range(4)]
            b, us = local_search(us, lambda: near_identity_monomial(n, q))
            worst = min(worst, b)
        print(f"monomial n={n} q={q}: running min margin {worst:.4f}")
    # HOC-type clocks with monomial matchers
    for q in [3, 9, 27]:
        x = np.arange(q)
        P = np.zeros((q, q))
        P[(x * pow(2, -1, q)) % q, x] = 1
        for _ in range(60):
            H = monomial(q, q)
            Cs = [np.linalg.matrix_power(H, j) @ P
                  @ np.linalg.matrix_power(H, -j) for j in range(4)]
            worst = min(worst, margin(Cs))
        print(f"HOC-monomial q={q}: running min margin {worst:.4f}")
    # Clifford / Weil family
    for p in [3, 5, 7]:
        gens = clifford_gens(p)
        for _ in range(30):
            us = [random_word(gens, 6) for _ in range(4)]
            b, us = local_search(us, lambda: random_word(gens, 1), steps=200)
            worst = min(worst, b)
        print(f"Clifford p={p}: running min margin {worst:.4f}")
    print(f"MIN MARGIN D - min(1/2, max||u-1||) = {worst:.6f}")
    assert worst >= -1e-9, "counterexample to (FIC-D)"
    print("OK: consistent with (FIC-D)")


if __name__ == "__main__":
    main()
