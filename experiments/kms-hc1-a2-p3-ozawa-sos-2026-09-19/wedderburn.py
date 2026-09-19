"""Symmetry group H = signed permutations of {a,b,c} (order 48) acting on Gamma_3 by automorphisms
x_i -> x_{perm(i)}^{sign(i)}, which preserve S = {a,b,c}^{+-1} and hence Delta.
Real orthogonal irreps of H are extracted numerically from the regular representation, then used to
block-diagonalise H-invariant Gram matrices on B_r (Wedderburn decomposition)."""
import itertools, numpy as np

def group_H():
    els = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            els.append((perm, signs))
    return els

def compose(h1, h2):
    """(h1 h2)(x) = h1(h2(x)): x_i -> h2 -> x_{p2 i}^{s2 i} -> x_{p1 p2 i}^{s1(p2 i) s2 i}."""
    p1, s1 = h1; p2, s2 = h2
    return (tuple(p1[p2[i]] for i in range(3)), tuple(s1[p2[i]] * s2[i] for i in range(3)))

def irreps(seed=1):
    H = group_H(); n = len(H); idx = {h: i for i, h in enumerate(H)}
    Lmat = []
    for h in H:
        M = np.zeros((n, n))
        for j, k in enumerate(H): M[idx[compose(h, k)], j] = 1
        Lmat.append(M)
    Rmat = []
    for h in H:
        M = np.zeros((n, n))
        for j, k in enumerate(H): M[idx[compose(k, h)], j] = 1
        Rmat.append(M)
    rng = np.random.default_rng(seed); c = rng.standard_normal(n)
    X = sum(c[i] * Rmat[i] for i in range(n)); X = X + X.T      # symmetric, commutes with L
    w, V = np.linalg.eigh(X)
    # group numerically equal eigenvalues
    groups = []; i = 0
    while i < n:
        j = i
        while j + 1 < n and abs(w[j + 1] - w[i]) < 1e-8: j += 1
        groups.append(V[:, i:j + 1]); i = j + 1
    reps, chars = [], []
    for E in groups:
        rho = [E.T @ L @ E for L in Lmat]
        ch = np.array([np.trace(m) for m in rho])
        if not any(np.allclose(ch, c2, atol=1e-6) for c2 in chars):
            chars.append(ch); reps.append(np.array(rho))
    assert sum(r.shape[1] ** 2 for r in reps) == n, "irreps incomplete"
    for r in reps:        # homomorphism and orthogonality check
        for a in range(n):
            assert np.allclose(r[a] @ r[a].T, np.eye(r.shape[1]), atol=1e-8)
        for a, b in [(3, 7), (11, 20), (5, 41)]:
            assert np.allclose(r[a] @ r[b], r[idx[compose(H[a], H[b])]], atol=1e-8)
    return H, reps

def adapted_bases(perm_action, reps, tol=1e-9):
    """perm_action: list over H of index arrays img[h][x] (permutation of range(N)).
    Returns list over irreps of (d, [U^(1),...,U^(d)]) with U^(k) of shape (N, m), orthonormal columns,
    such that every H-invariant P >= 0 is sum_rho sum_k U^(k) Q_rho U^(k)^T with Q_rho >= 0."""
    N = len(perm_action[0]); nH = len(perm_action); out = []
    for rho in reps:
        d = rho.shape[1]
        def proj(k, l, V):   # (d/|H|) sum_h rho(h)_{kl} pi(h) V ; pi(h) e_x = e_{h x}
            W = np.zeros_like(V)
            for h in range(nH):
                if abs(rho[h][k, l]) > 1e-14:
                    W[perm_action[h]] += rho[h][k, l] * V
            return W * (d / nH)
        P11 = proj(0, 0, np.eye(N))
        # orthonormal basis of the range of P11 (symmetric projection)
        w, V = np.linalg.eigh((P11 + P11.T) / 2)
        U1 = V[:, w > 0.5]
        m = U1.shape[1]
        Us = [U1] + [proj(k, 0, U1) for k in range(1, d)]
        out.append((d, Us))
    assert sum(d * U[0].shape[1] for d, U in out) == N
    return out
