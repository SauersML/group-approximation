"""Planted controls for census.py.

(1) Exact SU(2) lift of the triangle group Delta(4,3,5): U^4 = -1, V^3 = 1, (VU)^5 = 1 exactly.
    U = rotation by pi/2 lifted (eigenvalues e^{+-i pi/4}), V = rotation by 2 pi/3 lifted
    (eigenvalues e^{+-2 pi i/3}), axes at the angle theta that makes tr(VU) = 2 cos(4 pi/5).
    Prints the three defects there: pentagon ~ 0, r_1 and r_2 nonzero.
(2) The optimizer of census.py, run on that eigen-type with the pentagon word ONLY, must find
    defect ~ 0 (it recovers the planted solution from random starts).
"""
import math

import numpy as np
import torch

import census

CD = census.CD


def su2(axis, ang):
    """exp(-i ang/2 axis.sigma)"""
    sx = np.array([[0, 1], [1, 0]], complex)
    sy = np.array([[0, -1j], [1j, 0]], complex)
    sz = np.array([[1, 0], [0, -1]], complex)
    n = np.asarray(axis, float)
    n = n / np.linalg.norm(n)
    S = n[0] * sx + n[1] * sy + n[2] * sz
    return math.cos(ang / 2) * np.eye(2) - 1j * math.sin(ang / 2) * S


def planted():
    a, b = math.pi / 2, 4 * math.pi / 3  # U eigenvalues e^{-+ i pi/4}, V eigenvalues e^{-+ 2 pi i/3}
    ca, sa, cb, sb = math.cos(a / 2), math.sin(a / 2), math.cos(b / 2), math.sin(b / 2)
    target = math.cos(4 * math.pi / 5)  # tr(VU)/2
    ct = (ca * cb - target) / (sa * sb)
    th = math.acos(ct)
    U = su2([0, 0, 1], a)
    V = su2([math.sin(th), 0, math.cos(th)], b)
    return U, V, th


def main():
    U, V, th = planted()
    print(f"planted SU(2) triangle rep, axis angle theta = {th:.6f}")
    print("  U^4 + 1 =", np.abs(np.linalg.matrix_power(U, 4) + np.eye(2)).max())
    print("  V^3 - 1 =", np.abs(np.linalg.matrix_power(V, 3) - np.eye(2)).max())
    census.MODE = (0, 1, 2)
    d = census.opnorms(torch.tensor(U, dtype=CD), torch.tensor(V, dtype=CD))
    print(f"  defects: pentagon {d[0]:.2e}, r_1 {d[1]:.6f}, r_2 {d[2]:.6f}")
    print(f"  U eigenvalue angles/pi: {np.angle(np.linalg.eigvals(U)) / math.pi}")
    print(f"  V eigenvalue angles/pi: {np.angle(np.linalg.eigvals(V)) / math.pi}")

    # (2) optimizer recovery with the pentagon word only
    census.MODE = (0,)
    ue = [census.U_EIG[0], census.U_EIG[3]]
    ve = [census.V_EIG[1], census.V_EIG[2]]
    rng = np.random.default_rng(1)
    (val, Vb), = census.optimize_batch([(ue, ve)], 16, 600, rng)
    census.MODE = (0, 1, 2)
    d2 = census.opnorms(torch.diag(torch.tensor(ue, dtype=CD)), Vb)
    print(f"optimizer, pentagon only, type U(0,3) V(1,2): pentagon defect {val:.2e}; "
          f"at that point r_1 {d2[1]:.6f}, r_2 {d2[2]:.6f}")


if __name__ == "__main__":
    main()
