#!/usr/bin/env python3
"""Exhaust the one-qubit Clifford group for inner-conjugate antiphase lifts.

The enumeration uses double-precision matrices only as a finite design screen.
The promoted example ``(H, X H X)`` has the separate exact certificate
``H X H = Z`` and ``Z X = -X Z`` recorded in Cairn; no numerical tolerance is
used as proof of that identity or of any analytic claim.
"""

from collections import deque
import numpy as np


I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
Y = 1j * X @ Z
H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
S = np.array([[1, 0], [0, 1j]], dtype=complex)
PAULIS = {"I": I, "X": X, "Y": Y, "Z": Z}


def canonical(u):
    """Canonicalize a unitary modulo scalar phase."""
    flat = u.ravel()
    pivot = next(z for z in flat if abs(z) > 1e-9)
    v = u * np.exp(-1j * np.angle(pivot))
    v[np.abs(v) < 1e-10] = 0
    return tuple(np.round(v.real, 10).ravel()) + tuple(np.round(v.imag, 10).ravel())


def phase_equal(a, b):
    z = np.vdot(b.ravel(), a.ravel()) / np.vdot(b.ravel(), b.ravel())
    return abs(abs(z) - 1) < 1e-8 and np.linalg.norm(a - z * b) < 1e-8, z


def word_cliffords():
    seen = {canonical(I): (I, "I")}
    q = deque([(I, "I")])
    while q:
        u, w = q.popleft()
        for g, name in [(H, "H"), (S, "S")]:
            v, vw = g @ u, name + w
            k = canonical(v)
            if k not in seen:
                seen[k] = (v, vw)
                q.append((v, vw))
    return list(seen.values())


def main():
    cliff = word_cliffords()
    print(f"projective_clifford_count={len(cliff)}")
    hits = []
    for u, uw in cliff:
        for pn, p in PAULIS.items():
            v = p @ u @ p.conj().T
            anti_error = np.linalg.norm(u @ v + v @ u)
            comm = u @ v @ u.conj().T @ v.conj().T
            comm_error = np.linalg.norm(comm + I)
            if anti_error < 1e-8 and comm_error < 1e-8:
                hits.append((uw, pn, anti_error, comm_error))
    print(f"inner_conjugate_antiphase_hits={len(hits)}")
    for hit in hits:
        print(hit)


if __name__ == "__main__":
    main()
