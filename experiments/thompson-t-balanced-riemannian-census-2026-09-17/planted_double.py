"""Planted balanced control: k copies of the saved n=12 balanced minimiser (tag bal12).

Builds the k-fold direct sum in the census gauge, checks D, and polishes it monotonically
from the planted point and from perturbations exp(s*skew) that couple the copies.
If some polish goes below D(bal12), coupling copies lowers the balanced defect.
Usage: python3 planted_double.py <k> <source tag>
"""
import json, sys
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import CD, optimise, pair_from_U, diag_from_mult, exact_defects, A_EIG, B_EIG

SCR = '/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad'


def gauge(A, B, mA, mB):
    """Return U with A = U diag(dA) U^*, after permuting so that B = diag(dB)."""
    n = A.shape[0]
    dB = diag_from_mult(B_EIG, mB)
    bd = torch.diagonal(B)
    perm = []
    for e in B_EIG:
        perm += [j for j in range(n) if abs(complex(bd[j]) - e) < 1e-9]
    Pm = torch.eye(n, dtype=CD)[perm]
    A, B = Pm @ A @ Pm.T, Pm @ B @ Pm.T
    assert torch.allclose(torch.diagonal(B), dB)
    cols = []
    I = torch.eye(n, dtype=CD)
    for lam, m in zip(A_EIG, mA):
        P = I.clone()
        for mu in A_EIG:
            if mu != lam:
                P = P @ (A - mu * I) / (lam - mu)
        Uq, s, _ = torch.linalg.svd(P)
        cols.append(Uq[:, :m])
    U = torch.cat(cols, 1)
    return U, A, B


k, src = int(sys.argv[1]), sys.argv[2]
m1A, m1B = [3, 3, 3, 3], [4, 4, 4]
U1 = torch.load(SCR + '/U2_%s.pt' % src)
A1, B1 = pair_from_U(U1, diag_from_mult(A_EIG, m1A), diag_from_mult(B_EIG, m1B))
A = torch.block_diag(*[A1] * k)
B = torch.block_diag(*[B1] * k)
mA, mB = [3 * k] * 4, [4 * k] * 3
U, A2, B2 = gauge(A, B, mA, mB)
A3, B3 = pair_from_U(U, diag_from_mult(A_EIG, mA), diag_from_mult(B_EIG, mB))
res = dict(k=k, n=12 * k, source=src, D_single=max(exact_defects(A1, B1)),
           D_planted=max(exact_defects(A3, B3)), gauge_err=float((A3 - A2).abs().max()))
print(json.dumps(res), flush=True)
gen = torch.Generator().manual_seed(5)
res['polish'] = []
for s in [0.0, 0.05, 0.1, 0.2, 0.4]:
    n = 12 * k
    Z = (torch.randn(n, n, generator=gen) + 1j * torch.randn(n, n, generator=gen)).to(CD)
    S = (Z - Z.conj().T) * (s / (2 * n ** 0.5))
    D, _ = optimise(mA, mB, U0=U @ torch.linalg.matrix_exp(S), steps=1500, lr=0.01,
                    beta0=100.0, beta1=3000.0, monotone=True)
    res['polish'].append(dict(s=s, D=D))
    print('  s', s, 'D %.6f' % D, flush=True)
json.dump(res, open(__file__.rsplit('/', 1)[0] + '/out_planted_double_k%d_%s.json' % (k, src), 'w'), indent=1)
