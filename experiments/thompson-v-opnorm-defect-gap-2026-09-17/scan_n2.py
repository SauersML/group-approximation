"""Certified value of delta_2 (and delta_2 for the controls) by a Lipschitz grid scan.

For n = 2 and rho(a) = diag(1, -1), the normal form rho = rho4 * (W rho3 W^*) has W = diag(1, e^{i theta})
up to a scalar (which acts trivially by conjugation).  So D(rho) is a function of one angle theta.
The only k = 2 pattern is rho(a) = -1, forcing rho4 = sgn + sgn and rho3 = sgn + sgn, i.e. the scalar
character a, c -> -1, b -> 1; W then acts trivially and the scan evaluates it exactly.

Lipschitz bound.  theta -> W C W^* has derivative of norm ||[E, C]|| <= 1 with E = diag(0,1) a projection
and C unitary.  A word with m occurrences of c is then m-Lipschitz in theta, and so is ||r(rho_theta) - 1||
and the max over the four words.  With N grid points (spacing h = 2 pi / N) the true minimum is at least
min_grid - m_max * h / 2.

Usage: python3 scan_n2.py [--mode V] [--N 400000]
"""
import argparse, json, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import delta_n as dn  # noqa: E402


def mats(word, A, B, C):
    """Batched word evaluation; A, B fixed (2x2), C batched (N,2,2)."""
    N = C.shape[0]
    M = np.broadcast_to(np.eye(2, dtype=complex), (N, 2, 2)).copy()
    Binv = B.conj().T
    for l, e in word:
        if l == "c":
            M = M @ C
        elif l == "a":
            M = M @ A
        else:
            M = M @ (B if e > 0 else Binv)
    return M


def opnorm_minus_one(M):
    X = M - np.eye(2)
    return np.linalg.svd(X, compute_uv=False)[:, 0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="V")
    ap.add_argument("--N", type=int, default=400000)
    args = ap.parse_args()
    S4 = {k: dn.diagonalize_a(v)[0] for k, v in dn.s4_irreps().items()}
    S3 = {k: dn.diagonalize_a(v)[0] for k, v in dn.s3_irreps().items()}
    dn.check_relations(S4, S3)
    words = dn.load_words(args.mode)
    m_max = max(sum(1 for l, _ in w if l == "c") for w in words)
    theta = np.arange(args.N) * 2 * np.pi / args.N
    h = 2 * np.pi / args.N
    res = {"mode": args.mode, "N": args.N, "c_counts": [sum(1 for l, _ in w if l == "c") for w in words],
           "patterns": []}
    for p4, k4 in dn.patterns(S4, 2):
        for p3, k3 in dn.patterns(S3, 2):
            if k4 != k3 or k4 == 0:
                continue
            A4, B4 = dn.block_sum(S4, p4)[0]
            A3, C3 = dn.block_sum(S3, p3)[0]
            assert np.allclose(A4, A3)
            W = np.zeros((args.N, 2, 2), dtype=complex)
            W[:, 0, 0] = 1
            W[:, 1, 1] = np.exp(1j * theta)
            C = W @ C3.astype(complex) @ W.conj().transpose(0, 2, 1)
            D = np.max(np.stack([opnorm_minus_one(mats(w, A4.astype(complex), B4.astype(complex), C))
                                 for w in words], -1), -1)
            i = int(np.argmin(D))
            res["patterns"].append({"S4": p4, "S3": p3, "k": k4, "min_grid": float(D[i]),
                                    "theta_argmin": float(theta[i]),
                                    "certified_lower": float(D[i] - m_max * h / 2)})
    lows = [p for p in res["patterns"] if p["k"] == 1]
    res["delta2_upper"] = min(p["min_grid"] for p in res["patterns"])
    res["delta2_certified_lower_k1"] = min(p["certified_lower"] for p in lows)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
