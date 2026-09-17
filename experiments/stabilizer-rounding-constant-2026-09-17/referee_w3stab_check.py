#!/usr/bin/env python3
"""Independent second referee check (w3-stab, 2026-09-17) of the post-selection
induction proof of (SR*): stab(K) >= (1+c) lambda - c W, c = 1/sqrt2.

Written without reading the ref-04 scripts. It runs the recursion of the proof
literally (top eigenvector -> best term R -> post-select -> explicit Clifford U with
U A_R U^* = Z_n -> restrict to the code space -> recurse) and asserts at every level:

  S1  M = x_R >= 0 and a <= t(1+M) W_A                                   (1)
  S2  (I+A_R) K (I+A_R) = 2 (I+A_R) K_c  (operator identity)
  S3  <psi_1|K|psi_1> = lambda - a/(1+M)                                  (2)
  S4  every commuting term restricts to eps_Q B_Q with B_Q != I, and the
      restricted operator has 1-norm <= sum_C w_Q = W - w_R - W_A          (weight bound)
  S5  <v|K|v> = w_R + <v'|K'|v'> for v = psi_1 and for the rounded state   (3)
  S6  final state is a stabilizer state (exactly 2^n Paulis with |<P>| = 1)
      and <phi|K|phi> >= (1+c) lambda - c W

The final certificate S6 is a genuine lower bound on stab(K), so any ratio
(lambda - E)/(W - lambda) > 1/sqrt2 would be a counterexample to the proof.
Part B is an adversarial Nelder-Mead search maximizing that ratio.
"""
import itertools, sys
import numpy as np
from scipy.optimize import minimize

C = 1 / np.sqrt(2)
T = np.sqrt(2) - 1
TOL = 1e-8
P1 = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1, -1])]


def pmat(s):
    m = np.array([[1.0 + 0j]])
    for k in s:
        m = np.kron(m, P1[k])
    return m


def allstrings(n):
    return list(itertools.product(range(4), repeat=n))


def decompose(mat, n):
    """Pauli coefficients of a Hermitian matrix: dict string -> real coef."""
    d = {}
    for s in allstrings(n):
        v = np.trace(pmat(s) @ mat).real / 2 ** n
        if abs(v) > 1e-12:
            d[s] = v
    return d


def gate1(n, j, g):
    m = np.array([[1.0 + 0j]])
    for k in range(n):
        m = np.kron(m, g if k == j else np.eye(2))
    return m


def cnot(n, c, t):
    N = 2 ** n
    m = np.zeros((N, N), complex)
    for i in range(N):
        bits = [(i >> (n - 1 - k)) & 1 for k in range(n)]
        if bits[c]:
            bits[t] ^= 1
        j = sum(b << (n - 1 - k) for k, b in enumerate(bits))
        m[j, i] = 1
    return m


def swap(n, a, b):
    return cnot(n, a, b) @ cnot(n, b, a) @ cnot(n, a, b)


H1 = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
Sdg = np.diag([1, -1j])
X1 = P1[1]


def ident_pauli(mat, n):
    d = decompose(mat, n)
    assert len(d) == 1, d
    (s, v), = d.items()
    assert abs(abs(v) - 1) < 1e-9
    return s, np.sign(v)


def clifford_to_Zn(A, n):
    """Unitary U (a product of H, S^dag, CNOT, SWAP, X) with U A U^* = Z on the last qubit."""
    U = np.eye(2 ** n, dtype=complex)
    s, _ = ident_pauli(A, n)
    for j, k in enumerate(s):
        if k == 2:
            U = gate1(n, j, Sdg) @ U
        cur, _ = ident_pauli(U @ A @ U.conj().T, n)
        if cur[j] == 1:
            U = gate1(n, j, H1) @ U
    cur, _ = ident_pauli(U @ A @ U.conj().T, n)
    supp = [j for j in range(n) if cur[j] == 3]
    assert supp and all(cur[j] in (0, 3) for j in range(n))
    if n - 1 not in supp:
        U = swap(n, supp[0], n - 1) @ U
        supp = [n - 1 if j == supp[0] else j for j in supp]
    for j in supp:
        if j != n - 1:
            U = cnot(n, j, n - 1) @ U
    cur, sg = ident_pauli(U @ A @ U.conj().T, n)
    assert cur == tuple([0] * (n - 1) + [3]), cur
    if sg < 0:
        U = gate1(n, n - 1, X1) @ U
    Zn = gate1(n, n - 1, P1[3])
    assert np.allclose(U @ A @ U.conj().T, Zn)
    return U


stats = {"levels": 0, "min_slack1": np.inf, "max_err2": 0.0, "max_err_id": 0.0,
         "min_wslack": np.inf, "max_err3": 0.0, "idcomp": 0.0}


def reduce_terms(terms, n):
    """(R1),(R2): merge repeats, split off identity. terms: list of (coef, string)."""
    d = {}
    for b, s in terms:
        d[s] = d.get(s, 0.0) + b
    off = d.pop(tuple([0] * n), 0.0)
    return off, [(b, s) for s, b in d.items() if abs(b) > 1e-13]


def rounding(terms, n):
    """Returns stabilizer state phi following the proof, asserting S1-S5 on the way."""
    off, tt = reduce_terms(terms, n)
    N = 2 ** n
    if n == 0 or not tt:
        v = np.zeros(N, complex); v[0] = 1
        return v
    stats["levels"] += 1
    K0 = sum(b * pmat(s) for b, s in tt)
    ev, evec = np.linalg.eigh(K0)
    lam = ev[-1]; psi = evec[:, -1]
    ws = [abs(b) for b, s in tt]
    As = [np.sign(b) * pmat(s) for b, s in tt]
    xs = [np.vdot(psi, A @ psi).real for A in As]
    r = int(np.argmax(xs)); M = xs[r]; AR = As[r]
    assert M >= -1e-12, M
    Cidx, Aidx = [], []
    for q in range(len(tt)):
        if q == r:
            continue
        comm = AR @ As[q] - As[q] @ AR
        (Cidx if np.allclose(comm, 0) else Aidx).append(q)
        if q in Aidx:
            assert np.allclose(AR @ As[q] + As[q] @ AR, 0)
    WA = sum(ws[q] for q in Aidx)
    a = sum(ws[q] * xs[q] for q in Aidx)
    stats["min_slack1"] = min(stats["min_slack1"], T * (1 + M) * WA - a)       # S1
    assert a <= T * (1 + M) * WA + TOL
    KA = sum((ws[q] * As[q] for q in Aidx), np.zeros((N, N), complex))
    KC = sum((ws[q] * As[q] for q in Cidx), np.zeros((N, N), complex))
    Kc = ws[r] * AR + KC
    I = np.eye(N)
    stats["max_err_id"] = max(stats["max_err_id"],
                              np.abs((I + AR) @ K0 @ (I + AR) - 2 * (I + AR) @ Kc).max())  # S2
    Pi = (I + AR) / 2
    p1 = Pi @ psi; nrm2 = np.vdot(p1, p1).real
    assert abs(nrm2 - (1 + M) / 2) < 1e-9
    psi1 = p1 / np.sqrt(nrm2)
    e1 = np.vdot(psi1, K0 @ psi1).real
    stats["max_err2"] = max(stats["max_err2"], abs(e1 - (lam - a / (1 + M))))   # S3
    U = clifford_to_Zn(AR, n)
    even = np.arange(0, N, 2)   # last qubit |0>
    for q in Cidx:                                                              # S4
        B = (U @ As[q] @ U.conj().T)[np.ix_(even, even)]
        s, sg = ident_pauli(B, n - 1)
        assert s != tuple([0] * (n - 1)), "B_Q = I"
    Kp = (U @ KC @ U.conj().T)[np.ix_(even, even)]
    dK = decompose(Kp, n - 1)
    idc = abs(dK.get(tuple([0] * (n - 1)), 0.0))
    stats["idcomp"] = max(stats["idcomp"], idc)
    Wp = sum(abs(v) for v in dK.values())
    stats["min_wslack"] = min(stats["min_wslack"], sum(ws[q] for q in Cidx) - Wp)
    assert Wp <= sum(ws[q] for q in Cidx) + TOL
    # S5 at psi_1
    v1 = (U @ psi1)
    assert np.abs(v1[1::2]).max() < 1e-8
    v1p = v1[even]
    stats["max_err3"] = max(stats["max_err3"], abs(e1 - (ws[r] + np.vdot(v1p, Kp @ v1p).real)))
    # recurse with the explicit decomposition K' = sum_C w_Q eps_Q B_Q
    tp = []
    for q in Cidx:
        B = (U @ As[q] @ U.conj().T)[np.ix_(even, even)]
        s, sg = ident_pauli(B, n - 1)
        tp.append((ws[q] * sg, s))
    phip = rounding(tp, n - 1)
    phi = U.conj().T @ np.kron(phip, np.array([1, 0]))
    ephi = np.vdot(phi, K0 @ phi).real
    stats["max_err3"] = max(stats["max_err3"], abs(ephi - (ws[r] + np.vdot(phip, Kp @ phip).real)))
    return phi


def is_stabilizer(phi, n):
    cnt = sum(1 for s in allstrings(n) if abs(abs(np.vdot(phi, pmat(s) @ phi)) - 1) < 1e-8)
    return cnt == 2 ** n


def certify(terms, n, check_stab=True):
    off, tt = reduce_terms(terms, n)
    W = sum(abs(b) for b, s in terms)
    K = sum((b * pmat(s) for b, s in terms), np.zeros((2 ** n, 2 ** n), complex))
    lam = np.linalg.eigvalsh(K)[-1]
    phi = rounding(terms, n)
    if check_stab:
        assert is_stabilizer(phi, n)
    E = np.vdot(phi, K @ phi).real
    slack = E - ((1 + C) * lam - C * W)
    ratio = (lam - E) / (W - lam) if W - lam > 1e-9 else 0.0
    return slack, ratio


def rand_instance(rng, n, kind):
    S = allstrings(n)
    if kind == "dense":
        k = rng.integers(1, len(S) + 1)
        idx = rng.choice(len(S), size=k, replace=False)
        return [(rng.normal(), S[i]) for i in idx]
    if kind == "sparse":
        k = rng.integers(1, 5)
        idx = rng.choice(len(S), size=k, replace=False)
        return [(rng.exponential() * rng.choice([-1, 1]), S[i]) for i in idx]
    if kind == "repeats":   # repeated Paulis and identity terms in the input
        k = rng.integers(2, 8)
        return [(rng.normal(), S[rng.integers(len(S))]) for _ in range(k)]
    if kind == "anticomm":  # Jordan-Wigner Majoranas: pairwise anticommuting
        maj = []
        for j in range(n):
            maj.append(tuple([3] * j + [1] + [0] * (n - j - 1)))
            maj.append(tuple([3] * j + [2] + [0] * (n - j - 1)))
        k = rng.integers(1, len(maj) + 1)
        idx = rng.choice(len(maj), size=k, replace=False)
        return [(abs(rng.normal()), maj[i]) for i in idx]
    if kind == "neartight":  # (X+Z)/2 on each qubit plus a small perturbation
        t = []
        for j in range(n):
            t.append((0.5, tuple([0] * j + [1] + [0] * (n - j - 1))))
            t.append((0.5, tuple([0] * j + [3] + [0] * (n - j - 1))))
        for _ in range(rng.integers(0, 3)):
            t.append((0.05 * rng.normal(), S[rng.integers(len(S))]))
        return t
    raise ValueError(kind)


def main():
    rng = np.random.default_rng(20260917)
    kinds = ["dense", "sparse", "repeats", "anticomm", "neartight"]
    worst = (np.inf, None)
    maxratio = 0.0
    count = 0
    for n, reps in [(1, 400), (2, 400), (3, 250), (4, 60)]:
        for kind in kinds:
            for _ in range(reps // len(kinds) + 1):
                terms = rand_instance(rng, n, kind)
                slack, ratio = certify(terms, n, check_stab=(n <= 3))
                count += 1
                maxratio = max(maxratio, ratio)
                if slack < worst[0]:
                    worst = (slack, (n, kind))
    print(f"A: {count} random instances n<=4; min slack of rounded state {worst[0]:.3e} at {worst[1]}; "
          f"max ratio (lambda-E)/(W-lambda) = {maxratio:.9f}")
    print("   per-step extremes:", {k: (float(v)) for k, v in stats.items()})

    # B: adversarial search maximizing the ratio of the proof's rounding
    best = 0.0
    for n in (1, 2, 3):
        S = [s for s in allstrings(n) if any(s)]
        for trial in range({1: 20, 2: 20, 3: 8}[n]):
            k = min(len(S), rng.integers(2, 7))
            supp = [S[i] for i in rng.choice(len(S), size=k, replace=False)]

            def f(x):
                terms = list(zip(x, supp))
                W = sum(abs(v) for v in x)
                if W < 1e-6:
                    return 0.0
                _, r = certify(terms, n, check_stab=False)
                return -r
            x0 = rng.normal(size=k)
            res = minimize(f, x0, method="Nelder-Mead", options={"maxiter": 600, "xatol": 1e-10, "fatol": 1e-12})
            r = -res.fun
            _, r2 = certify(list(zip(res.x, supp)), n, check_stab=True)  # re-check at optimum
            best = max(best, r2)
    print(f"B: adversarial Nelder-Mead on the rounding ratio, n<=3: best ratio {best:.9f} (1/sqrt2 = {C:.9f})")
    ok = maxratio <= C + 1e-9 and best <= C + 1e-9 and worst[0] > -1e-9
    print("RESULT:", "no violation" if ok else "VIOLATION")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
