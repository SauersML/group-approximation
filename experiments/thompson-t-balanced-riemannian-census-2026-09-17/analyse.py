"""Structure of a census minimiser saved by two_stage.py.

Prints the three relator defects, the commutant dimension (1 = irreducible), the
near-central quantity gamma = ||[A^2, B] - 1||, the spectrum of C = B A (phases in units
of 2 pi / 60), and the dimensions of the joint invariant subspaces found by
diagonalising a random element of the commutant.
Usage: python3 analyse.py <tag> <multA comma> <multB comma>
"""
import json, sys
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import CD, pair_from_U, diag_from_mult, exact_defects, A_EIG, B_EIG

SCR = '/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad'


def commutant_basis(A, B, tol=1e-6):
    n = A.shape[0]
    I = torch.eye(n, dtype=CD)
    L = torch.cat([torch.kron(A, I) - torch.kron(I, A.T.contiguous()),
                   torch.kron(B, I) - torch.kron(I, B.T.contiguous())], 0)
    _, s, Vh = torch.linalg.svd(L)
    null = (s < tol * float(s[0])).sum()
    # vec is row-major: X.reshape(-1); kron(A,I) vec(X) = vec(A X), kron(I,A^T) vec(X) = vec(X A)
    return [Vh[-j - 1].conj().reshape(n, n) for j in range(int(null))]


def blocks(A, B):
    basis = commutant_basis(A, B)
    g = torch.Generator().manual_seed(3)
    X = sum(complex(torch.randn(1, generator=g)) * M for M in basis)
    H = X + X.conj().T
    ev = torch.linalg.eigvalsh(H)
    # cluster eigenvalues of a random hermitian commutant element
    ev = sorted(float(x) for x in ev)
    groups, cur = [], [ev[0]]
    for x in ev[1:]:
        if abs(x - cur[-1]) < 1e-5:
            cur.append(x)
        else:
            groups.append(len(cur)); cur = [x]
    groups.append(len(cur))
    return len(basis), groups


tag = sys.argv[1]
mA = [int(x) for x in sys.argv[2].split(',')]
mB = [int(x) for x in sys.argv[3].split(',')]
U = torch.load(SCR + '/U2_%s.pt' % tag)
A, B = pair_from_U(U, diag_from_mult(A_EIG, mA), diag_from_mult(B_EIG, mB))
n = A.shape[0]
J = A @ A
gamma = float(torch.linalg.matrix_norm(J @ B @ J.conj().T @ B.conj().T - torch.eye(n, dtype=CD), ord=2))
C = B @ A
ph = torch.angle(torch.linalg.eigvals(C)) / (2 * torch.pi) * 60
cd, grp = blocks(A, B)
rec = dict(tag=tag, n=n, defects=exact_defects(A, B), D=max(exact_defects(A, B)), gamma=gamma,
           commutant_dim=cd, isotypic_block_sizes=grp,
           C_phases_60ths=sorted(round(float(x), 3) for x in ph))
print(json.dumps(rec))
json.dump(rec, open(__file__.rsplit('/', 1)[0] + '/out_analyse_%s.json' % tag, 'w'), indent=1)
