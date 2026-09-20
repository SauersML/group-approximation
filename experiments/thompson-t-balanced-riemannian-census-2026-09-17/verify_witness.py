"""Export and verify the balanced n = 12 witness (tag bal12).

Mode 'export': read the scratchpad U2_bal12.pt and write witness_bal12.json (real and imaginary
parts of U, and the multiplicities), so the witness is stored with the experiment.
Mode 'verify' (default): from witness_bal12.json alone, in float64 (numpy),
  * eta = ||U^* U - 1||_op                       (U is unitary up to eta),
  * the exact eigen-relations: A = U diag(dA) U^*, B = diag(dB), so after polar correction
    U~ = U (U^*U)^(-1/2) the pair (U~ dA U~^*, B) satisfies A^4 = B^3 = 1 exactly with the
    balanced multiplicities 3,3,3,3 and 4,4,4,
  * D = max ||r - 1||_op over r1, r2, rP for the float pair, and the certified bound
    D(exact) <= D + 20 * 2 * eta * (1 + eta)^40 + 1e-12   (Lipschitz in the 20 A-letters of r2),
  * the two smallest singular values of the commutant operator X -> ([A,X], [B,X]):
    the smallest is ~ 0 (scalars), the second is the irreducibility margin.
"""
import json, sys
import numpy as np

HERE = __file__.rsplit('/', 1)[0]
W = np.exp(2j * np.pi / 3)
A_EIG = [1, 1j, -1, -1j]
B_EIG = [1, W, W.conjugate()]


def diag_from_mult(eigs, mult):
    v = []
    for e, m in zip(eigs, mult):
        v += [e] * m
    return np.array(v, dtype=complex)


def relators(A, B):
    Ai, Bi = A.conj().T, B.conj().T
    X, Xi = B @ A @ B, Bi @ Ai @ Bi
    J = A @ A
    Y, Yi = J @ X @ J, J @ Xi @ J
    Wm, Wi = J @ B @ B @ J, J @ B @ J
    Z, Zi = Wm @ X @ Wi, Wm @ Xi @ Wi
    BA = B @ A
    return [X @ Y @ Xi @ Yi, X @ Z @ Xi @ Zi, np.linalg.matrix_power(BA, 5)]


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'verify'
    if mode == 'export':
        import torch
        U = torch.load('/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad/U2_bal12.pt').numpy()
        json.dump(dict(multA=[3, 3, 3, 3], multB=[4, 4, 4], U_re=U.real.tolist(), U_im=U.imag.tolist()),
                  open(HERE + '/witness_bal12.json', 'w'))
        print('exported')
        return
    w = json.load(open(HERE + '/witness_bal12.json'))
    U = np.array(w['U_re']) + 1j * np.array(w['U_im'])
    n = U.shape[0]
    I = np.eye(n)
    eta = np.linalg.norm(U.conj().T @ U - I, 2)
    dA, dB = diag_from_mult(A_EIG, w['multA']), diag_from_mult(B_EIG, w['multB'])
    A = U @ np.diag(dA) @ U.conj().T
    B = np.diag(dB)
    defs = [float(np.linalg.norm(r - I, 2)) for r in relators(A, B)]
    D = max(defs)
    bound = D + 40 * eta * (1 + eta) ** 40 + 1e-12
    L = np.vstack([np.kron(A, I) - np.kron(I, A.T), np.kron(B, I) - np.kron(I, B.T)])
    s = np.linalg.svd(L, compute_uv=False)
    J = A @ A
    gamma = float(np.linalg.norm(J @ B @ J.conj().T @ B.conj().T - I, 2))
    out = dict(n=n, multA=w['multA'], multB=w['multB'], eta=float(eta),
               A4_err=float(np.linalg.norm(np.linalg.matrix_power(A, 4) - I, 2)),
               defects=defs, D=D, certified_upper_bound=bound,
               commutant_smallest_two_singular_values=[float(s[-1]), float(s[-2])],
               gamma_A2B_commutator=gamma,
               trA=abs(np.trace(A)) / n, trB=abs(np.trace(B)) / n,
               trBA=abs(np.trace(B @ A)) / n)
    print(json.dumps(out, indent=1))
    json.dump(out, open(HERE + '/out_verify_witness_bal12.json', 'w'), indent=1)


main()
