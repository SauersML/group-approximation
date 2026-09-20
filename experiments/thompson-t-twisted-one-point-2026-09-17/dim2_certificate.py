"""Certificate for mu_2 = mu_1 = 2 sin(pi/24) (twisted one-point gap in dimension 2).

Setting: U, V in U(2), U^4 = -1, V^3 = 1 exactly, both non-scalar (the scalar cases reduce to
direct sums of characters, handled in the node's proof). Up to simultaneous conjugation
    U = diag(u1, u2)  (u1 != u2 odd 8th roots),   V(th) = R(th) diag(v1, v2) R(th)^T,
    R(th) = [[cos(th/2), -sin(th/2)], [sin(th/2), cos(th/2)]],   th in [0, pi],   v1 != v2 cube roots.
f(th) = max(||(VU)^5 - 1||, ||r_1 - 1||, ||r_2 - 1||).

Lipschitz: ||dV/dth|| = ||(1/2)[K, V]|| <= 1 with K = R'(0). The pentagon word has 5 letters V,
r_1 = X Y1 - Y1 X has derivative <= 2 (||X'|| + ||Y1'||) <= 2 (2 + 2) = 8,
r_2 = X Y2 - Y2 X has derivative <= 2 (2 + 6) = 16. So f is 16-Lipschitz, and on a grid of step h
f >= min_grid f - 8 h.

Families: the ordered pairs {u1,u2} (6 unordered) x ordered (v1,v2) (3 unordered x 2 orders are the
same family with th -> pi - th; we take both orders over [0,pi], which is harmless and redundant).

The delicate family is U = diag(e^{i pi/4}, e^{-i pi/4}), (v1, v2) = (w^2, w), the only one whose
endpoint is a direct sum of two optimal characters. There det VU = 1, VU is in SU(2) with eigenvalues
e^{+-i phi}, cos phi = tr(VU)/2 strictly monotone in th, and the pentagon defect is 2|sin(5 phi/2)|.
It is >= mu_1 unless 5 phi lies within pi/12 of 4 pi. On the complementary th-interval (plus a
collar) we certify max(r_1, r_2) defects by the grid.
"""
import itertools
import json
import math

import numpy as np

MU1 = 2 * math.sin(math.pi / 24)
UE = [np.exp(1j * math.pi * (2 * k + 1) / 4) for k in range(4)]
VE = [np.exp(2j * math.pi * j / 3) for j in range(3)]
LIP = 16.0


def R(th):
    c, s = math.cos(th / 2), math.sin(th / 2)
    return np.array([[c, -s], [s, c]], complex)


def defects(U, V):
    X = V @ U @ V
    J = U @ U
    Ji = J.conj().T
    W = J @ V @ V @ J
    Wi = W.conj().T
    VU = V @ U
    P = np.linalg.matrix_power(VU, 5)
    Y1 = J @ X @ Ji
    Y2 = W @ X @ Wi
    n = lambda M: np.linalg.norm(M, 2)
    return n(P - np.eye(2)), n(X @ Y1 - Y1 @ X), n(X @ Y2 - Y2 @ X)


def family(iu, iv, grid):
    U = np.diag([UE[iu[0]], UE[iu[1]]])
    D = np.diag([VE[iv[0]], VE[iv[1]]])
    out = []
    for th in grid:
        Rt = R(th)
        out.append(defects(U, Rt @ D @ Rt.T))
    return np.array(out)


def main():
    h = math.pi / 20000
    grid = np.linspace(0, math.pi, 20001)
    report = {"mu1": MU1, "h": h, "lipschitz": LIP, "families": []}
    delicate = ((0, 3), (2, 1))
    # (0,3),(1,2) is the same family with v1, v2 swapped: V(th) with swapped D equals
    # (diag(1,-1) R(pi - th)) D (diag(1,-1) R(pi - th))^T, and diag(1,-1) commutes with U. So it is certified
    # together with the delicate family and skipped in the generic grid.
    mirror = ((0, 3), (1, 2))
    ok = True
    for iu in itertools.combinations(range(4), 2):
        for iv in itertools.permutations(range(3), 2):
            d = family(iu, iv, grid)
            f = d.max(1)
            fam = {"U": iu, "V": iv, "min_f": float(f.min()), "argmin_th": float(grid[f.argmin()])}
            if (iu, iv) not in (delicate, mirror):
                lower = float(f.min()) - LIP * h / 2
                fam["certified_lower"] = lower
                fam["certified_gt_mu1"] = lower > MU1
                ok &= lower > MU1
            report["families"].append(fam)
    # delicate family
    iu, iv = delicate
    U = np.diag([UE[iu[0]], UE[iu[1]]])
    D = np.diag([VE[iv[0]], VE[iv[1]]])
    # exact trace formula: tr(V U) for V = R D R^T is linear in cos th
    def trVU(th):
        Rt = R(th)
        return np.trace(Rt @ D @ Rt.T @ U)
    t0, tpi = trVU(0.0), trVU(math.pi)
    # tr(VU) = a + b cos th with a = (t0 + tpi)/2, b = (t0 - tpi)/2  (entries of R D R^T are affine in cos th, sin th;
    # the sin th terms multiply the off-diagonal of D-conjugate and vanish against diagonal U in the trace)
    a, b = (t0 + tpi) / 2, (t0 - tpi) / 2
    chk = max(abs(trVU(th) - (a + b * math.cos(th))) for th in np.linspace(0, math.pi, 97))
    phi0 = math.acos((t0 / 2).real)
    phipi = math.acos((tpi / 2).real)
    # window where the pentagon defect < mu1: 5 phi in (4 pi - pi/12, 4 pi + pi/12)
    lo_phi, hi_phi = (4 * math.pi - math.pi / 12) / 5, (4 * math.pi + math.pi / 12) / 5
    th_of_phi = lambda ph: math.acos((2 * math.cos(ph) - a.real) / b.real)
    th_lo, th_hi = th_of_phi(lo_phi), th_of_phi(hi_phi)
    collar = 0.01
    sub = np.linspace(max(0.0, th_lo - collar), min(math.pi, th_hi + collar), 4001)
    hs = sub[1] - sub[0]
    d = family(iu, iv, sub)
    rmax = d[:, 1:].max(1)
    lower_r = float(rmax.min()) - LIP * hs / 2
    ok &= lower_r > MU1
    report["delicate"] = {
        "U": iu, "V": iv,
        "trace_affine_check": float(chk), "imag_trace_max": float(abs(t0.imag) + abs(tpi.imag)),
        "phi_at_0_over_pi": phi0 / math.pi, "phi_at_pi_over_pi": phipi / math.pi,
        "pentagon_window_th": [th_lo, th_hi],
        "r_window_certified_lower": lower_r,
        "r1_min_on_window": float(d[:, 1].min()), "r2_min_on_window": float(d[:, 2].min()),
        "pentagon_at_th0": float(defects(U, D)[0]),
    }
    report["certified_mu2_eq_mu1"] = bool(ok)
    print(json.dumps(report, indent=1, default=str))


if __name__ == "__main__":
    main()
