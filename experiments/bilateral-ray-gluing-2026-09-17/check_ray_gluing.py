"""Ray gluing check for laurent-finitary-el-is-kazhdan-lef-inside-doubled-jacobson.

W = F_2[Z] is identified with F_2[N] (+) F_2[N] by e_k -> (e_k, 0) for k >= 0 and
e_(-1-k) -> (0, e_k).  J = F_2<S,T | TS=1> acts on F_2[N] by S e_k = e_(k+1),
T e_0 = 0, T e_(k+1) = e_k.  Q = 1 - ST.

Checked on a finite window [-M, M) of Z (and [0, M) of N), away from the window edge:
  (1) rho(z) = [[S, Q], [0, T]] and rho(z^-1) = [[T, 0], [Q, S]];
  (2) rho(e_00) = diag(Q, 0);
  (3) u = [[S,Q],[0,T]] is invertible with the stated inverse (as J-words: ST+Q=1, QS=0, TQ=0, TS=1);
  (4) rho is multiplicative on random products of Laurent-plus-finitary operators;
  (5) the symbol of rho(a) is diag(a(z), a(z^-1)): the J-blocks of rho(z^d) far from the corner
      are S^d / T^d Toeplitz bands.
All arithmetic is over F_2 with numpy int arrays mod 2.
"""
import numpy as np

rng = np.random.default_rng(20260918)
M = 60          # window half-width on Z; F_2[N] window is [0, M)
D = 2 * M       # dimension of the Z-window
K = 6           # support radius of random finitary parts and degree bound of Laurent parts
SAFE = 20       # only compare entries with both indices at distance >= SAFE from the window edge


def zidx(k):
    return k + M          # Z-site k in [-M, M) -> index


def glue(k):
    """Z-site k -> (block, N-site)."""
    return (0, k) if k >= 0 else (1, -1 - k)


def glued_index(k):
    b, j = glue(k)
    return b * M + j


# permutation matrix phi: W-window -> F_2[N]^2 window
PHI = np.zeros((D, D), dtype=np.int64)
for k in range(-M, M):
    PHI[glued_index(k), zidx(k)] = 1


def laurent(coeffs):
    """coeffs: dict d -> 0/1, operator sum_d c_d z^d on the Z-window (truncated)."""
    A = np.zeros((D, D), dtype=np.int64)
    for d, c in coeffs.items():
        if c % 2 == 0:
            continue
        for k in range(-M, M):
            if -M <= k + d < M:
                A[zidx(k + d), zidx(k)] ^= 1
    return A


def finitary(entries):
    A = np.zeros((D, D), dtype=np.int64)
    for (a, b) in entries:
        A[zidx(a), zidx(b)] ^= 1
    return A


def rho(A):
    return (PHI @ A @ PHI.T) % 2


# J operators on the N-window [0, M)
S = np.zeros((M, M), dtype=np.int64)
T = np.zeros((M, M), dtype=np.int64)
for k in range(M - 1):
    S[k + 1, k] = 1
    T[k, k + 1] = 1
I_N = np.eye(M, dtype=np.int64)
Q = (I_N - S @ T) % 2
Z0 = np.zeros((M, M), dtype=np.int64)


def block(a, b, c, d):
    return np.block([[a, b], [c, d]]) % 2


def safe_mask_glued():
    """entries of F_2[N]^2 whose N-sites are < M - SAFE (far from the truncation edge)."""
    ok = np.zeros(D, dtype=bool)
    for b in range(2):
        for j in range(M - SAFE):
            ok[b * M + j] = True
    return np.outer(ok, ok)


MASK = safe_mask_glued()


def agree(X, Y):
    return bool(np.all((X % 2)[MASK] == (Y % 2)[MASK]))


results = {}
U = block(S, Q, Z0, T)
Uinv = block(T, Z0, Q, S)
results["rho(z) = [[S,Q],[0,T]]"] = agree(rho(laurent({1: 1})), U)
results["rho(z^-1) = [[T,0],[Q,S]]"] = agree(rho(laurent({-1: 1})), Uinv)
results["rho(e_00) = diag(Q,0)"] = agree(rho(finitary([(0, 0)])), block(Q, Z0, Z0, Z0))
results["u u^-1 = 1 (window)"] = agree((U @ Uinv) % 2, np.eye(D, dtype=np.int64))
results["u^-1 u = 1 (window)"] = agree((Uinv @ U) % 2, np.eye(D, dtype=np.int64))
# exact J-word identities behind (3): ST + Q = 1, QS = 0, TQ = 0, TS = 1 (TS exact away from edge)
inner = slice(0, M - SAFE)
results["ST + Q = 1"] = bool(np.all(((S @ T + Q) % 2)[inner, inner] == I_N[inner, inner]))
results["QS = 0"] = bool(np.all(((Q @ S) % 2)[inner, inner] == 0))
results["TQ = 0"] = bool(np.all(((T @ Q) % 2)[inner, inner] == 0))
results["TS = 1"] = bool(np.all(((T @ S) % 2)[inner, inner] == I_N[inner, inner]))


def random_rbi():
    coeffs = {d: int(rng.integers(0, 2)) for d in range(-K // 2, K // 2 + 1)}
    ents = [(int(rng.integers(-K, K)), int(rng.integers(-K, K))) for _ in range(int(rng.integers(0, 5)))]
    return (laurent(coeffs) + finitary(ents)) % 2


mult_ok = True
for _ in range(200):
    A, B = random_rbi(), random_rbi()
    if not agree(rho((A @ B) % 2), (rho(A) @ rho(B)) % 2):
        mult_ok = False
        break
results["rho multiplicative on 200 random products"] = mult_ok

# (5) symbol: far from the corner, rho(z^d) is S^d on block (0,0) and T^d on block (1,1), zero off-diagonal
sym_ok = True
for d in range(1, 5):
    R = rho(laurent({d: 1}))
    Sd = np.linalg.matrix_power(S, d) % 2
    Td = np.linalg.matrix_power(T, d) % 2
    far = slice(d + 2, M - SAFE)
    if not (np.all(R[:M, :M][far, far] == Sd[far, far]) and np.all(R[M:, M:][far, far] == Td[far, far])
            and np.all(R[:M, M:][far, far] == 0) and np.all(R[M:, :M][far, far] == 0)):
        sym_ok = False
results["symbol of rho(z^d) is diag(z^d, z^-d), d=1..4"] = sym_ok

for k, v in results.items():
    print(f"{'PASS' if v else 'FAIL'}  {k}")
print("ALL PASS" if all(results.values()) else "SOME FAILED")
