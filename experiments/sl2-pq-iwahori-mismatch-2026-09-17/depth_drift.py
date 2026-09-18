"""Exact check of the depth-drift certificate for the q-adic Iwahori mismatch.

For an irrep tau of I' = I / K(q^(k+1)) put
    d0(tau) = least a >= 1 with tau trivial on K(q^a)      (capped at k+1),
    d1(tau) = least b >= 1 with tau trivial on K_1(q^b)    (capped at k+1),
    Phi = d1 - d0,
where K_1(q^b) = g K(q^b) g^-1 = {a,d = 1 mod q^b, b = 0 mod q^(b+1), c = 0 mod q^(b-1)}.
The certificate is g(tau) = Phi(tau) for tau nontrivial and g(trivial) = -c,
c = (q-1)/(q+1).  The theorem says, for every irrep chi of SL_2(Z/q^k):
    chi nontrivial:  E_{chi|I} g >= c   (restriction through K_0)
                     E_{chi|I} g <= -c  (restriction through K_1)
    chi trivial:     g = -c on both sides.
Hence 2 eps >= E_0 g - E_1 g >= 2 c (1 - theta_0), i.e. eps >= (1-theta_0) c.
All quantities below are exact rationals (multiplicities are integers).

Usage: python3 depth_drift.py q k
"""
import sys
from fractions import Fraction
import numpy as np
from mismatch_lp import build, trivial_index


def kernel_depths(I, q, k):
    """d0, d1 of every irrep of I' (rows of I.tab)."""
    E = I.els
    Mi = q ** (k + 1)
    def trivial_on(mask):
        cl = np.unique(I.cls[mask])
        return np.all(np.abs(I.tab[:, cl] - I.degs[:, None]) < 1e-6, axis=1)
    d0 = np.full(len(I.degs), k + 1)
    d1 = np.full(len(I.degs), k + 1)
    for a in range(k, 0, -1):
        m = q ** a
        maskK = (E[:, 0] % m == 1) & (E[:, 3] % m == 1) & (E[:, 1] % m == 0) & (E[:, 2] % m == 0)
        maskK1 = ((E[:, 0] % m == 1) & (E[:, 3] % m == 1)
                  & (E[:, 1] % (q * m) == 0) & (E[:, 2] % (m // q) == 0))
        assert Mi % (q * m) == 0
        d0[trivial_on(maskK)] = a
        d1[trivial_on(maskK1)] = a
    return d0, d1


def main():
    q, k = int(sys.argv[1]), int(sys.argv[2])
    G, I, R0, R1 = build(q, k)
    d0, d1 = kernel_depths(I, q, k)
    phi = d1 - d0
    c = Fraction(q - 1, q + 1)
    tI = trivial_index(I)
    g = [Fraction(int(v)) for v in phi]
    g[tI] = -c
    tG = trivial_index(G)
    print(f"q={q} k={k} |I'|={I.n} irreps(I')={len(I.degs)} Phi values={sorted(set(phi.tolist()))}")
    worst0, worst1 = None, None
    for i in range(len(G.degs)):
        deg = int(G.degs[i])
        e0 = sum(int(R0[i, j]) * int(I.degs[j]) * g[j] for j in range(len(g))) / deg
        e1 = sum(int(R1[i, j]) * int(I.degs[j]) * g[j] for j in range(len(g))) / deg
        if i == tG:
            assert e0 == -c and e1 == -c
            continue
        # constituents of sigma_0 have d0 <= k, of sigma_1 have d1 <= k: Phi in {-1,0,1}
        worst0 = e0 if worst0 is None else min(worst0, e0)
        worst1 = e1 if worst1 is None else max(worst1, e1)
    print(f"  min over nontrivial chi of E_(chi|I via K_0) g = {worst0}   (need >= {c})")
    print(f"  max over nontrivial chi of E_(chi|I via K_1) g = {worst1}   (need <= {-c})")
    assert worst0 >= c and worst1 <= -c
    print(f"  certified: eps >= (1 - theta_0) * {c} for all level-{k} pairs")


if __name__ == "__main__":
    main()
