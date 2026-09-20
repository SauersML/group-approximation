"""Evaluate the planted direct sum of k copies of the dimension-2 optimum, rewritten in the
census gauge (B diagonal with sorted eigenvalues, A = U D_A U^*), and re-optimise from it."""
import math, sys
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import CD, B_EIG, exact_defects, optimise

T2 = 0.20297212652182536  # argmin from control_n2 refinement


def planted(k):
    v = torch.tensor([math.cos(T2 / 2), math.sin(T2 / 2)], dtype=CD)
    P = torch.outer(v, v.conj())
    I2 = torch.eye(2, dtype=CD)
    A2 = 1j * P - 1j * (I2 - P)
    B2 = torch.diag(torch.tensor([B_EIG[1], B_EIG[2]], dtype=CD))
    A = torch.block_diag(*[A2] * k)
    B = torch.block_diag(*[B2] * k)
    # permutation putting all w-coordinates first
    perm = [2 * j for j in range(k)] + [2 * j + 1 for j in range(k)]
    Pm = torch.eye(2 * k, dtype=CD)[perm]
    A, B = Pm @ A @ Pm.T, Pm @ B @ Pm.T
    # A = U D U^*, D = diag(i..i, -i..-i)
    ev, V = torch.linalg.eig(A)
    order = sorted(range(2 * k), key=lambda j: -ev[j].imag)
    U = V[:, order]
    U, _ = torch.linalg.qr(U)
    return A, B, U


if __name__ == '__main__':
    for k in [1, 3, 6]:
        A, B, U = planted(k)
        print('k', k, 'planted D', ['%.6f' % x for x in exact_defects(A, B)])
        D, _ = optimise([0, k, 0, k], [0, k, k], U0=U, steps=600, beta0=200.0)
        print('   re-optimised from planted (non-monotone scheme):', '%.6f' % D)
