"""Check the exact reducing block X_xi inside Ad(V (+) V tensor U).

For random unitaries V (a x a) and U (b x b), M = V (+) (V tensor U).
Ad M acts on M_{a(1+b)} (HS space).  X_xi : eta -> eta tensor xi sits in the
off-diagonal block Hom(C^a, C^a tensor C^b).  We verify
  Ad M X_xi = X_{U xi}     (exact),
that the projection onto K = span{X_xi} commutes with Ad M, and that for a
symmetric average h = (1/|S|) sum Ad M(s) the spectrum of the U-average is
contained in the spectrum of h.
"""
import numpy as np

rng = np.random.default_rng(0)


def haar(n):
    z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


a, b = 3, 2
D = a * (1 + b)


def M_of(V, U):
    M = np.zeros((D, D), complex)
    M[:a, :a] = V
    M[a:, a:] = np.kron(V, U)
    return M


def X(xi):
    Xm = np.zeros((D, D), complex)
    Xm[a:, :a] = np.kron(np.eye(a), xi.reshape(b, 1))  # eta -> eta tensor xi
    return Xm


def adj_matrix(M):
    # vec(M X M^*) = (conj(M) kron M) vec(X) with column-major vec
    return np.kron(M.conj(), M)


def vec(Xm):
    return Xm.reshape(-1, order="F")


gens = [(haar(a), haar(b)) for _ in range(2)]

err = 0.0
for V, U in gens:
    M = M_of(V, U)
    for _ in range(5):
        xi = rng.standard_normal(b) + 1j * rng.standard_normal(b)
        err = max(err, np.abs(M @ X(xi) @ M.conj().T - X(U @ xi)).max())
print("max intertwining error:", err)

basis = np.stack([vec(X(e)) for e in np.eye(b)], axis=1)
Q, _ = np.linalg.qr(basis)
P = Q @ Q.conj().T
Ads = [adj_matrix(M_of(V, U)) for V, U in gens]
comm = max(np.abs(P @ A - A @ P).max() for A in Ads)
print("max commutator [P, Ad M]:", comm)

H = (np.eye(D * D) + sum(A + A.conj().T for A in Ads)) / 5
Hu = (np.eye(b) + sum(U + U.conj().T for _, U in gens)) / 5
sH = np.linalg.eigvalsh((H + H.conj().T) / 2)
sU = np.linalg.eigvalsh(Hu)
dist = max(np.min(np.abs(sH - x)) for x in sU)
print("max distance of sp(U-average) from sp(Ad M-average):", dist)
assert err < 1e-12 and comm < 1e-12 and dist < 1e-10
print("OK")
