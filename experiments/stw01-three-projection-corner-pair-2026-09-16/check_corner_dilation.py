"""Numerical sanity check for the corner dilation (Lemma 1.1), Lemma 4.1(3) and the
phase-tuning estimates (Theorem 2, Step B) of
research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md.

The quasitrace is replaced by the normalized matrix trace, which is a trace. This checks
the algebra and the numerical constants only, not any quasitrace statement.
Single-threaded, deterministic seed, small output.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np

rng = np.random.default_rng(20260916)
ETA = 1.0 / 32.0


def rand_pos_contraction(n, lo=0.0, hi=1.0):
    g = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    u, _ = np.linalg.qr(g)
    d = rng.uniform(lo, hi, n)
    return (u * d) @ u.conj().T


def psd_sqrt(x):
    w, v = np.linalg.eigh((x + x.conj().T) / 2)
    w = np.clip(w, 0, None)
    return (v * np.sqrt(w)) @ v.conj().T


def dilation(a, b, theta):
    n = a.shape[0]
    I = np.eye(n)
    Z0 = np.zeros((n, n))
    va = np.vstack([psd_sqrt(a), psd_sqrt(I - a)])
    vb = np.vstack([psd_sqrt(b), np.exp(1j * theta) * psd_sqrt(I - b)])
    P1 = np.block([[I, Z0], [Z0, Z0]])
    P2 = va @ va.conj().T
    P3 = vb @ vb.conj().T
    w = va.conj().T @ vb
    return P1, P2, P3, va, vb, w


def err(x):
    return float(np.max(np.abs(x)))


def main():
    worst = {}
    def upd(k, v):
        worst[k] = max(worst.get(k, 0.0), v)

    n = 6
    for trial in range(200):
        a = rand_pos_contraction(n)
        b = rand_pos_contraction(n)
        theta = rng.uniform(0, 2 * np.pi)
        P1, P2, P3, va, vb, w = dilation(a, b, theta)
        I = np.eye(n)
        Z0 = np.zeros((n, n))
        for P in (P1, P2, P3):
            upd("projection", err(P @ P - P) + err(P - P.conj().T))
        upd("P1P2P1=a+0", err(P1 @ P2 @ P1 - np.block([[a, Z0], [Z0, Z0]])))
        upd("P1P3P1=b+0", err(P1 @ P3 @ P1 - np.block([[b, Z0], [Z0, Z0]])))
        Wa = np.hstack([va, np.zeros((2 * n, n))])
        upd("WaWa*=P2,Wa*Wa=P1", err(Wa @ Wa.conj().T - P2) + err(Wa.conj().T @ Wa - P1))
        Z = np.hstack([va @ w, np.zeros((2 * n, n))])
        upd("ZZ*=P2P3P2", err(Z @ Z.conj().T - P2 @ P3 @ P2))
        upd("Z*Z=w*w+0", err(Z.conj().T @ Z - np.block([[w.conj().T @ w, Z0], [Z0, Z0]])))
        wformula = psd_sqrt(a) @ psd_sqrt(b) + np.exp(1j * theta) * psd_sqrt(I - a) @ psd_sqrt(I - b)
        upd("w formula", err(w - wformula))
        # beta: r2 -> 1 - r2, r3 -> 1 - r3; check tr((1-P2)(1-P3)(1-P2)) = tr(1-P2) - tr((1-P2)P3(1-P2))
        J = np.eye(2 * n)
        lhs = np.trace((J - P2) @ (J - P3) @ (J - P2))
        rhs = np.trace(J - P2) - np.trace(P3 @ (J - P2) @ P3)
        upd("beta word identity (trace)", abs(lhs - rhs))

    # Step B estimates with spectra in [1/2 - eta, 1/2 + eta]
    fmin0, fmaxpi = 1.0, 0.0
    ivt_ok = True
    for trial in range(200):
        x = rand_pos_contraction(n)
        y = rand_pos_contraction(n)
        tx = np.trace(x).real / n
        ty = np.trace(y).real / n
        I = np.eye(n)
        a = (0.5 - ETA * tx) * I + ETA * x
        b = (0.5 - ETA * ty) * I + ETA * y
        upd("tau(a)=1/2", abs(np.trace(a).real / n - 0.5))
        ev = np.concatenate([np.linalg.eigvalsh(a), np.linalg.eigvalsh(b)])
        upd("spectrum outside [1/2-eta,1/2+eta]", max(0.0, float(np.max(np.abs(ev - 0.5)) - ETA)))
        def f(th):
            _, _, _, _, _, w = dilation(a, b, th)
            return np.trace(w.conj().T @ w).real / n
        f0, fpi = f(0.0), f(np.pi)
        fmin0 = min(fmin0, f0)
        fmaxpi = max(fmaxpi, fpi)
        ivt_ok = ivt_ok and (f0 > 0.5 > fpi)
        _, _, _, _, _, w0 = dilation(a, b, 0.0)
        _, _, _, _, _, wpi = dilation(a, b, np.pi)
        upd("||w0 - 1|| - 4 eta", max(0.0, np.linalg.norm(w0 - I, 2) - 4 * ETA))
        upd("||w_pi|| - 4 eta", max(0.0, np.linalg.norm(wpi, 2) - 4 * ETA))
        upd("||w0*w0 - 1|| - 17/64", max(0.0, np.linalg.norm(w0.conj().T @ w0 - I, 2) - 17 / 64))

    for k, v in worst.items():
        print(f"{k:40s} max error {v:.2e}")
    print(f"min f(0)  = {fmin0:.6f}  (bound 47/64 = {47/64:.6f})")
    print(f"max f(pi) = {fmaxpi:.6f}  (bound 1/64 = {1/64:.6f})")
    print("IVT sign condition holds in all trials:", ivt_ok)


if __name__ == "__main__":
    main()
