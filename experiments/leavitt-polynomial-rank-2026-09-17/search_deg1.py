# Search over F_2 for homogeneous degree-1 commuting pairs in L_{F2}(1,2).
# A degree-1 element with window r is x = sum_{u,w,c} (A_c)_{w,u} s_{wc} t_u  (|u|=|w|=r),
# i.e. a pair (A_0,A_1) of N x N matrices (N <= 2^r, zero-padded).
# x y = y x  iff  A_c B_d = B_c A_d for all letters c,d.
# The degree-n monomial x^i y^(n-i) is the tensor  word c_1..c_n -> A_{c1}..A_{ci} B_{c(i+1)}..B_{cn}.
# x,y algebraically independent iff for every n these n+1 tensors are linearly independent.
import itertools, random, sys
import numpy as np

def rank2(M):
    M = (M % 2).astype(np.uint8).copy()
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r

def monomial_tensor(A, B, i, n):
    N = A[0].shape[0]
    out = []
    for word in itertools.product((0, 1), repeat=n):
        P = np.eye(N, dtype=np.int64)
        for pos, c in enumerate(word):
            P = (P @ (A[c] if pos < i else B[c])) % 2
        out.append(P.flatten())
    return np.concatenate(out) % 2

def hilbert(A, B, nmax):
    h = []
    for n in range(1, nmax + 1):
        T = np.array([monomial_tensor(A, B, i, n) for i in range(n + 1)])
        h.append(rank2(T))
    return h

def commute(A, B):
    return all((((A[c] @ B[d]) - (B[c] @ A[d])) % 2 == 0).all() for c in (0, 1) for d in (0, 1))

def allmats(N):
    for bits in range(1 << (N * N)):
        yield np.array([(bits >> k) & 1 for k in range(N * N)], dtype=np.int64).reshape(N, N)

def nullspace_B(A, N):
    # linear map B=(B0,B1) -> (A_c B_d - B_c A_d)_{c,d}; return basis of kernel over F_2
    dim = 2 * N * N
    cols = []
    for k in range(dim):
        v = np.zeros(dim, dtype=np.int64); v[k] = 1
        B = [v[:N*N].reshape(N, N), v[N*N:].reshape(N, N)]
        img = np.concatenate([((A[c] @ B[d] - B[c] @ A[d]) % 2).flatten() for c in (0, 1) for d in (0, 1)])
        cols.append(img)
    M = np.array(cols).T % 2  # rows = equations, cols = unknowns
    # gaussian elimination to find kernel
    M = M.astype(np.uint8).copy()
    rows, ncols = M.shape
    pivcols = []; r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]: M[i] ^= M[r]
        pivcols.append(c); r += 1
    free = [c for c in range(ncols) if c not in pivcols]
    basis = []
    for f in free:
        v = np.zeros(ncols, dtype=np.int64); v[f] = 1
        for i, pc in enumerate(pivcols):
            if M[i, f]: v[pc] = 1
        basis.append(v)
    return basis

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    samples = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    random.seed(1)
    best = {}
    def As():
        if samples == 0:
            for A0 in allmats(N):
                for A1 in allmats(N):
                    yield [A0, A1]
        else:
            for _ in range(samples):
                yield [np.array([[random.randint(0, 1) for _ in range(N)] for _ in range(N)]) for _ in range(2)]
    count = 0
    for A in As():
        basis = nullspace_B(A, N)
        if len(basis) <= 1:
            continue
        # try a few B in the kernel (random combinations)
        for _ in range(min(8, 2 ** len(basis))):
            coeffs = [random.randint(0, 1) for _ in basis]
            v = sum(c * b for c, b in zip(coeffs, basis)) % 2 if basis else None
            B = [v[:N*N].reshape(N, N), v[N*N:].reshape(N, N)]
            h = hilbert(A, B, nmax)
            key = tuple(h)
            if key not in best:
                best[key] = (A, B)
                print(key, flush=True)
            count += 1
    print("tested", count)
    print("max final rank", max(k[-1] for k in best))
