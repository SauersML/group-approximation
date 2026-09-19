"""q-adic Iwahori mismatch c_k(theta) for K_0 = SL_2(Z_q), K_1 = g K_0 g^-1, g = diag(q,1).

sigma_0 : smooth rep of K_0 of level k  (= rep of SL_2(Z/q^k)),
sigma_1 : smooth rep of K_1 of level k  (= rep of SL_2(Z/q^k) pulled back by x -> g^-1 x g),
I = K_0 cap K_1 = {b = 0 mod q}.  Both restrictions to I factor through I' = I / K(q^(k+1)).

    c_k(theta) = min  (1/2) sum_psi dim(psi) |m_0(psi) - m_1(psi)|  / d
                 over sigma_0, sigma_1 of equal dimension d with
                 (K_0-trivial multiplicity of sigma_0) <= theta * d,

i.e. the least fraction of sigma_0|_I that has no partner in sigma_1|_I.
The LP is scale invariant, so any rational optimum is realised by honest
representations.  We print the primal optimum and an exact rational
dual certificate (a lower bound verified in Fractions).

Usage: python3 mismatch_lp.py q k [theta]
"""
import sys
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from chartab import MatGroup


def sl2_elements(M, cond=None):
    r = np.arange(M)
    A, B, C, D = np.meshgrid(r, r, r, r, indexing="ij")
    E = np.stack([A.ravel(), B.ravel(), C.ravel(), D.ravel()], axis=1)
    keep = (E[:, 0] * E[:, 3] - E[:, 1] * E[:, 2]) % M == 1
    if cond is not None:
        keep &= cond(E)
    E = E[keep]
    ident = np.where((E == [1, 0, 0, 1]).all(1))[0][0]
    E[[0, ident]] = E[[ident, 0]]
    return E


def build(q, k):
    Mg, Mi = q ** k, q ** (k + 1)
    G = MatGroup(sl2_elements(Mg), Mg).classes().character_table()
    I = MatGroup(sl2_elements(Mi, lambda E: E[:, 1] % q == 0), Mi).classes().character_table()
    R = I.els[I.reps]
    phi0 = R % Mg
    phi1 = np.stack([R[:, 0], R[:, 1] // q, q * R[:, 2], R[:, 3]], axis=1) % Mg
    out = []
    for phi in (phi0, phi1):
        gcls = G.cls[G.index(phi)]
        chiG = G.tab[:, gcls]                       # [chi, I-class]
        m = (chiG * I.csize) @ I.tab.conj().T / I.n  # [chi, psi]
        mi = np.round(m.real).astype(int)
        assert np.abs(m - mi).max() < 1e-6 and (mi >= 0).all()
        assert (mi @ I.degs == G.degs).all()
        out.append(mi)
    return G, I, out[0], out[1]


def trivial_index(G):
    t = np.where(np.abs(G.tab - 1).max(1) < 1e-8)[0]
    assert len(t) == 1
    return int(t[0])


def lp(G, I, R0, R1, theta):
    nG, nI = len(G.degs), len(I.degs)
    triv = trivial_index(G)
    # variables: x (nG), y (nG), t (nI)
    c = np.concatenate([np.zeros(2 * nG), I.degs / 2.0])
    Aub, bub = [], []
    for s in (1, -1):   # s*(R0^T x - R1^T y) - t <= 0
        Aub.append(np.hstack([s * R0.T, -s * R1.T, -np.eye(nI)]))
        bub.append(np.zeros(nI))
    row = np.zeros(2 * nG + nI); row[triv] = 1; row[:nG] -= theta * G.degs
    Aub.append(row[None, :]); bub.append([0.0])
    Aeq = np.zeros((2, 2 * nG + nI)); Aeq[0, :nG] = G.degs; Aeq[1, nG:2 * nG] = G.degs
    res = linprog(c, A_ub=np.vstack(Aub), b_ub=np.concatenate(bub), A_eq=Aeq,
                  b_eq=[1, 1], bounds=(0, None), method="highs")
    assert res.status == 0
    return res


def certified_lower_bound(G, I, R0, R1, theta, f):
    """Weak duality: for |f_psi| <= dim(psi)/2,
    mismatch >= min_x x.(R0 f) - max_y y.(R1 f).  Exact in Fractions."""
    degs = [int(v) for v in G.degs]
    a = [sum(Fraction(int(R0[i, j])) * f[j] for j in range(len(f))) for i in range(len(degs))]
    b = [sum(Fraction(int(R1[i, j])) * f[j] for j in range(len(f))) for i in range(len(degs))]
    maxy = max(b[i] / degs[i] for i in range(len(degs)))
    # min over x >= 0, sum x_i deg_i = 1, x_0 <= theta: greedy on ratio a_i/deg_i
    ratios = sorted(range(len(degs)), key=lambda i: a[i] / degs[i])
    mass, val = Fraction(0), Fraction(0)
    for i in ratios:
        cap = Fraction(theta) if i == trivial_index(G) else Fraction(1) - mass
        take = min(cap, Fraction(1) - mass)   # mass measured in dimension
        val += take * a[i] / degs[i]; mass += take
        if mass == 1:
            break
    return val - maxy


def main():
    q, k = int(sys.argv[1]), int(sys.argv[2])
    theta = Fraction(sys.argv[3]) if len(sys.argv) > 3 else Fraction(1, 2)
    G, I, R0, R1 = build(q, k)
    print(f"q={q} k={k} |G|={G.n} classes(G)={G.r} |I'|={I.n} classes(I')={I.r} theta={theta}")
    res = lp(G, I, R0, R1, float(theta))
    nG, nI = len(G.degs), len(I.degs)
    print(f"primal optimum c_k(theta) ~ {res.fun:.6f}")
    x, y = res.x[:nG], res.x[nG:2 * nG]
    print("  sigma_0 support (deg: weight*deg):",
          {int(G.degs[i]): round(float(x[i] * G.degs[i]), 4) for i in np.where(x > 1e-9)[0]})
    print("  sigma_1 support (deg: weight*deg):",
          {int(G.degs[i]): round(float(y[i] * G.degs[i]), 4) for i in np.where(y > 1e-9)[0]})
    # dual certificate from HiGHS marginals on the two t-constraint blocks
    lam = -res.ineqlin.marginals
    f = lam[:nI] - lam[nI:2 * nI]
    fr = []
    for j in range(nI):
        v = Fraction(f[j]).limit_denominator(10 ** 6)
        cap = Fraction(int(I.degs[j]), 2)
        fr.append(max(-cap, min(cap, v)))
    lb = certified_lower_bound(G, I, R0, R1, theta, fr)
    print(f"exact certified lower bound c_k(theta) >= {lb} = {float(lb):.6f}")


if __name__ == "__main__":
    main()
