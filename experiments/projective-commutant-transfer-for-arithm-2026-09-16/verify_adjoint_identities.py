"""Numerical sanity check of the elementary identities (AP0)-(AP8) used in
research/adjoint-regular-rcc-projective-transfer-proof.md.

Checks, on random Haar unitaries and on tensor/direct-sum/adjoint
constructions:
  AP0  ||XY-YX||_2 = ||XYX*Y* - I||_2
  AP1  ||Ad W - I||_2^2 = 2 - 2|tr W|^2,  tr Ad W = |tr W|^2
  AP2  Ad[U,V] = [Ad U, Ad V]
  AP3  ||Ad V - I||_2^2 <= 2||V - I||_2^2
  AP4  ||V (x) W - I||_2 <= ||V - I||_2 + ||W - I||_2
  AP5  tr(W (+) I) = (1+tr W)/2,  1-|tr(W (+) I)|^2 <= ||W-I||_2^2/2
  AP6  ||W - I||_2^2 <= 4 (1 - |tr(W (+) I)|^2)
  tensor invariance: [U (x) I, V (x) Z] = [U,V] (x) I
  AP8  ||Ad(U~) Ad(V~) - Ad(V~) Ad(U~)||_2^2 = 2(1-|tr[U,V]|^2)
       for U~=U (x) I, V~=V (x) Z.
Also a projective (twisted) example: V with U V U* = z V for a scalar z != 1
(clock and shift matrices), where the source energy is 0 but the ordinary
commutator is far from I; the adjoint witness commutes exactly.

Single-threaded, deterministic seed, tiny dimensions.  Run:
  OMP_NUM_THREADS=1 timeout 600 python3 verify_adjoint_identities.py
"""
import numpy as np

rng = np.random.default_rng(20260916)
TOL = 1e-9


def haar(k):
    z = (rng.standard_normal((k, k)) + 1j * rng.standard_normal((k, k))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    d = np.diag(r)
    return q * (d / np.abs(d))


def tr(x):
    return np.trace(x) / x.shape[0]


def hs(x):
    return np.sqrt(np.real(np.trace(x.conj().T @ x)) / x.shape[0])


def comm(u, v):
    return u @ v @ u.conj().T @ v.conj().T


def ad(w):
    return np.kron(w, w.conj())


def dsum_id(w):
    k = w.shape[0]
    out = np.eye(2 * k, dtype=complex)
    out[:k, :k] = w
    return out


def main():
    worst = {}

    def rec(name, val):
        worst[name] = max(worst.get(name, -np.inf), val)

    for trial in range(200):
        k = int(rng.integers(2, 6))
        m = int(rng.integers(1, 4))
        U, V, W, Z = haar(k), haar(k), haar(k), haar(m)
        # partially commuting examples to probe small-energy regime
        if trial % 4 == 0:
            eps = 10.0 ** (-rng.integers(1, 6))
            H = rng.standard_normal((k, k)) + 1j * rng.standard_normal((k, k))
            H = (H + H.conj().T) / 2
            ev, P = np.linalg.eigh(H)
            W = P @ np.diag(np.exp(1j * eps * ev)) @ P.conj().T
        I = np.eye(k)
        rec("AP0", abs(hs(U @ V - V @ U) - hs(comm(U, V) - I)))
        rec("AP1a", abs(hs(ad(W) - np.eye(k * k)) ** 2 - (2 - 2 * abs(tr(W)) ** 2)))
        rec("AP1b", abs(tr(ad(W)) - abs(tr(W)) ** 2))
        rec("AP2", hs(ad(comm(U, V)) - comm(ad(U), ad(V))))
        rec("AP3", hs(ad(W) - np.eye(k * k)) ** 2 - 2 * hs(W - I) ** 2)
        VW = np.kron(V, Z)
        rec("AP4", hs(VW - np.eye(k * m)) - hs(V - I) - hs(Z - np.eye(m)))
        t = tr(W)
        rec("AP5a", abs(tr(dsum_id(W)) - (1 + t) / 2))
        rec("AP5b", (1 - abs(tr(dsum_id(W))) ** 2) - hs(W - I) ** 2 / 2)
        rec("AP6", hs(W - I) ** 2 - 4 * (1 - abs(tr(dsum_id(W))) ** 2))
        Ut = np.kron(U, np.eye(m))
        Vt = np.kron(V, Z)
        rec("tensor", hs(comm(Ut, Vt) - np.kron(comm(U, V), np.eye(m))))
        lhs = hs(ad(Ut) @ ad(Vt) - ad(Vt) @ ad(Ut)) ** 2
        rec("AP8", abs(lhs - 2 * (1 - abs(tr(comm(U, V))) ** 2)))

    # twisted example: clock and shift
    k = 12
    omega = np.exp(2j * np.pi / k)
    clock = np.diag(omega ** np.arange(k))
    shift = np.roll(np.eye(k), 1, axis=0)
    c = comm(clock, shift)
    twisted_energy = 1 - abs(tr(c)) ** 2
    ordinary_dist = hs(clock @ shift - shift @ clock)
    adjoint_dist = hs(ad(clock) @ ad(shift) - ad(shift) @ ad(clock))

    print("worst deviations (should be <= ~1e-9 for equalities, <= 1e-9 for inequalities):")
    ok = True
    for name, val in worst.items():
        flag = val <= TOL
        ok = ok and flag
        print(f"  {name:7s} {val: .3e} {'ok' if flag else 'FAIL'}")
    print(f"twisted clock/shift k=12: source commutator scalar={np.round(c[0,0],6)}, "
          f"trace-square energy={twisted_energy:.2e}, "
          f"||XY-YX||_2={ordinary_dist:.4f}, adjoint ||.||_2={adjoint_dist:.2e}")
    ok = ok and twisted_energy < TOL and adjoint_dist < TOL and ordinary_dist > 0.5
    print("ALL OK" if ok else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
