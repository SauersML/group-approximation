"""Small GF(2) linear algebra helpers (numpy uint8 arrays)."""
import numpy as np


def rref(M):
    M = (M.copy() % 2).astype(np.uint8)
    rows, cols = M.shape
    piv = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + nz[0]
        if p != r:
            M[[r, p]] = M[[p, r]]
        mask = M[:, c].copy()
        mask[r] = 0
        idx = np.nonzero(mask)[0]
        if len(idx):
            M[idx] ^= M[r]
        piv.append(c)
        r += 1
    return M[:r], piv


def rank(M):
    return len(rref(M)[1])


def nullspace(M):
    """Basis (rows) of {x : M x = 0}."""
    rows, cols = M.shape
    R, piv = rref(M)
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        x = np.zeros(cols, dtype=np.uint8)
        x[f] = 1
        for i, p in enumerate(piv):
            if R[i, f]:
                x[p] = 1
        basis.append(x)
    return np.array(basis, dtype=np.uint8).reshape(len(basis), cols)


def solve(M, b):
    """One solution x of M x = b, or None."""
    rows, cols = M.shape
    aug = np.concatenate([M % 2, (b % 2).reshape(-1, 1)], axis=1).astype(np.uint8)
    R, piv = rref(aug)
    if cols in piv:
        return None
    x = np.zeros(cols, dtype=np.uint8)
    for i, p in enumerate(piv):
        x[p] = R[i, cols]
    return x


def mm(*Ms):
    out = Ms[0] % 2
    for M in Ms[1:]:
        out = (out.astype(np.int64) @ M.astype(np.int64)) % 2
    return out.astype(np.uint8)
