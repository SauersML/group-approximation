#!/usr/bin/env python3
"""Spectrum of the compressed conjugation map Phi = E_Z Ad(V) on the
37-dim witness algebra, at the control-optimal dictionary V.

Basis: orbit matrices E_i (pairwise HS-orthogonal, ||E_i||^2 = |O_i|).
Phi matrix: Phi_{ij} = <E_i, V E_j V*> / |O_i| (so Phi(E_j) = sum_i
Phi_{ij} E_i after E_Z).  Hermitian part spectrum on the trace-zero,
identity-orthogonal subspace decides the floor criterion.
"""
import json
import sys

import numpy as np

exec(open("sl3_delta3_probe_v3.py").read().split("def main()")[0])


def main():
    NOR, LAB = orbit_reps()
    mats = [(LAB == i).astype(np.float64) for i in range(NOR)]
    osize = np.array([m_.sum() for m_ in mats])
    pl = [(perm_of(a), perm_of(b)) for a, b in PLIST]
    pli = [(inv_perm(a), inv_perm(b)) for a, b in pl]

    def defect_V(V):
        f = 0.0
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            f += 2 - 2 * np.real(np.trace(W[pbi, :]) / D)
        return f

    rng2 = np.random.default_rng(777)
    V = np.linalg.qr(rng2.normal(size=(D, D)) +
                     1j * rng2.normal(size=(D, D)))[0]
    step = 0.5
    for it in range(260):
        f0 = defect_V(V)
        NV = np.zeros((D, D), dtype=complex)
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            NV += -(2.0 / D) * (W[:, pbi] - W[pb, :])
        Y = (NV - NV.conj().T) / 2.0
        nn = max(np.linalg.norm(Y), 1e-14)
        A = (step / nn) * Y
        V2 = np.linalg.solve(np.eye(D) - A / 2, (np.eye(D) + A / 2) @ V)
        if defect_V(V2) < f0:
            V = V2
            step = min(step * 1.2, 1.0)
        else:
            step *= 0.5
            if step < 1e-7:
                break
    D0 = defect_V(V)

    # Phi matrix in the E-basis (weighted orthogonal basis)
    Phi = np.zeros((NOR, NOR), dtype=complex)
    for j in range(NOR):
        T = V @ mats[j] @ V.conj().T
        for i in range(NOR):
            Phi[i, j] = np.vdot(mats[i], T) / osize[i]
    # HS inner product on Z: <x, y> = sum_i conj(x_i) y_i osize_i / D
    # orthonormal basis: F_i = E_i / sqrt(osize_i); Phi in F-basis:
    S = np.diag(np.sqrt(osize))
    Sinv = np.diag(1.0 / np.sqrt(osize))
    PhiF = S @ Phi @ Sinv
    H = (PhiF + PhiF.conj().T) / 2.0
    # identity of Z in F-coords: id = sum over diagonal-orbit E_i;
    # diagonal orbits: those supported on the diagonal
    diag_orbs = [i for i in range(NOR) if (mats[i] * np.eye(D)).sum() > 0]
    idv = np.zeros(NOR)
    for i in diag_orbs:
        idv[i] = np.sqrt(osize[i])
    idv /= np.linalg.norm(idv)
    # trace functional: tau(E_i) = tr(E_i)/D nonzero only diagonal orbits
    trv = np.zeros(NOR)
    for i in diag_orbs:
        trv[i] = (mats[i] * np.eye(D)).sum() / np.sqrt(osize[i])
    trv /= np.linalg.norm(trv)
    # project H to the orthogonal complement of the trace vector
    # (trace-zero subspace of Z in F-coords)
    P = np.eye(NOR) - np.outer(trv, trv)
    Hred = P @ H @ P
    ev = np.sort(np.linalg.eigvalsh(Hred))
    out = {"D0": round(float(D0), 5),
           "phi_herm_spectrum_low6": [round(float(x), 5) for x in ev[:6]],
           "phi_herm_spectrum_high3": [round(float(x), 5) for x in ev[-3:]],
           "n_negative": int((ev < -1e-9).sum()),
           "n_positive": int((ev > 1e-9).sum())}
    print(json.dumps(out, indent=1), flush=True)
    with open("sl3_phi_spectrum.json", "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", file=sys.stderr)


main()
