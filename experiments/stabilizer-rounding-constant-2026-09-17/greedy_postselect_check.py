#!/usr/bin/env python3
"""Run the rounding of the proof of (SR*) (post-select the top eigenvector on its term of largest
expectation, recurse on the code space) on random Pauli sums, and check that the resulting
stabilizer energy is >= (1+c) lambda - c W with c = 1/sqrt2.
Run: nice -n 10 timeout 1200 python3 greedy_postselect_check.py trials seed
"""
import sys, json, itertools
import numpy as np

I2 = np.eye(2); X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1, -1])
PM = {'I': I2, 'X': X, 'Y': Y, 'Z': Z}
def mat(l):
    out = np.array([[1.0 + 0j]])
    for ch in l: out = np.kron(out, PM[ch])
    return out
def commute(a, b):
    return sum(1 for p, q in zip(a, b) if p != 'I' and q != 'I' and p != q) % 2 == 0

c = 1 / np.sqrt(2)
trials = int(sys.argv[1]); rng = np.random.default_rng(int(sys.argv[2]))
worst = 1e9; count = 0
for tr in range(trials):
    n = int(rng.integers(1, 5))
    labs = [''.join(p) for p in itertools.product('IXYZ', repeat=n) if set(p) != {'I'}]
    k = int(rng.integers(2, min(len(labs), 10) + 1))
    chosen = list(rng.choice(len(labs), size=k, replace=False))
    beta = {labs[i]: float(rng.normal()) for i in chosen}
    if tr % 3 == 0:  # bias towards near-frustration-free instances
        beta = {l: b * (4 if i == 0 else 1) for i, (l, b) in enumerate(beta.items())}
    W = sum(abs(b) for b in beta.values()); K = sum(b * mat(l) for l, b in beta.items())
    lam = np.linalg.eigvalsh(K)[-1]
    # rounding
    d = 2 ** n; Proj = np.eye(d); gens = []  # signed chosen Paulis as matrices
    const = 0.0; live = dict(beta)
    while True:
        # drop terms anticommuting with a chosen generator; terms in +-group of chosen become constants
        Kl = sum((b * mat(l) for l, b in live.items()), np.zeros((d, d)))
        vals, vecs = np.linalg.eigh(Proj @ Kl @ Proj + (-1e6) * (np.eye(d) - Proj))
        psi = vecs[:, -1]
        nonconst = {}
        for l, b in live.items():
            A = np.sign(b) * mat(l); PA = Proj @ A @ Proj
            s = np.trace(PA).real / np.trace(Proj).real
            if np.allclose(PA, s * Proj, atol=1e-9) and abs(abs(s) - 1) < 1e-9:
                const += abs(b) * s
            else:
                nonconst[l] = b
        if not nonconst: break
        R = max(nonconst, key=lambda l: np.real(np.conj(psi) @ (np.sign(nonconst[l]) * mat(l)) @ psi))
        AR = np.sign(nonconst[R]) * mat(R)
        Proj = Proj @ (np.eye(d) + AR) / 2
        live = {l: b for l, b in nonconst.items() if l != R and commute(l, R)}
        const += abs(nonconst[R])
    bound = (1 + c) * lam - c * W
    slack = const - bound; worst = min(worst, slack / max(W, 1e-12)); count += 1
    if slack < -1e-9:
        print("VIOLATION", beta, const, bound); sys.exit(1)
print(json.dumps({"trials": count, "min_normalized_slack": worst}))
