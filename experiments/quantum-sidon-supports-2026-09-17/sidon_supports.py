"""Numerical checks for sidon-neighbourhood-quantum-endomorphisms-are-automorphisms.

Checks, on small tensor regions:
  E1  split wiring over Z, d = 6 = 2*3, N = {0,1}, conjugated by random site unitaries:
      support algebras are factors with k_min product = d, the site-1 supports of
      Phi(A_0) and Phi(A_1) commute and generate M_6, and Phi(A_0) = tensor of supports.
  E2  teeth: cluster entangler over Z (d = 2, N = {-1,0,1}, overlaps of size 2):
      site supports of Phi(A_0) and Phi(A_1) do NOT commute, so the slice lemma really
      needs one-site overlaps.
  E3  why k_min and not dim/centre: B = {x (+) lambda 1_5} in M_10 and its commutant
      commute, dim/centre product 169 > 100 = d^2, while k_min product 1 <= 10.
  E4  lemma (a) instance: M_4 embedded diagonally in (M_2 (+) M_2) (x) M_2 (x) C^2 style:
      k_min product >= d; the support x (+) u x u* is abstractly M_2 (k_min is the size
      of the smallest irreducible representation of the abstract algebra).

Run with OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 (threaded BLAS stalls in the sandbox).
Output: sidon_supports-output.txt
"""
import itertools
import numpy as np

rng = np.random.default_rng(20260917)
TOL = 1e-8


def orth(mats, n):
    if not mats:
        return []
    V = np.array([m.reshape(-1) for m in mats]).T
    U, s, _ = np.linalg.svd(V, full_matrices=False)
    r = int((s > TOL * max(1.0, s[0])).sum())
    return [U[:, i].reshape(n, n) for i in range(r)]


def closure(gens, n):
    B = orth([np.eye(n, dtype=complex)] + list(gens) + [g.conj().T for g in gens], n)
    while True:
        prods = [a @ b for a, b in itertools.product(B, B)]
        B2 = orth(B + prods, n)
        if len(B2) == len(B):
            return B2
        B = B2


def kron_all(ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out


def slices(x, dims, site):
    """Span of slices (omega (x) id)(x) at tensor position `site`."""
    k = len(dims)
    t = x.reshape(dims + dims)
    perm = [site] + [i for i in range(k) if i != site]
    t = t.transpose(perm + [k + p for p in perm])
    ds = dims[site]
    dr = int(np.prod(dims)) // ds
    t = t.reshape(ds, dr, ds, dr).transpose(0, 2, 1, 3).reshape(ds * ds, dr * dr)
    U, s, _ = np.linalg.svd(t, full_matrices=False)
    r = int((s > TOL * max(1.0, s[0])).sum())
    return [U[:, i].reshape(ds, ds) for i in range(r)]


def support(alg, dims, site):
    sl = []
    for x in alg:
        sl += slices(x, dims, site)
    return closure(orth(sl, dims[site]), dims[site])


def centre(alg, n):
    # solve [z, b] = 0 for z in span(alg)
    rows = []
    for b in alg:
        rows.append(np.array([(z @ b - b @ z).reshape(-1) for z in alg]).T)
    Mx = np.vstack(rows)
    _, s, Vh = np.linalg.svd(Mx)
    null = Vh[(s > TOL).sum():].conj()
    extra = Vh.shape[0] - len(s)
    return [sum(c * z for c, z in zip(v, alg)) for v in null], extra


def blocks(alg, n):
    Z, _ = centre(alg, n)
    Z = orth(Z, n)
    c = sum(rng.normal() * (z + z.conj().T) for z in Z)
    w, v = np.linalg.eigh(c)
    groups = []
    for val in w:
        if not any(abs(val - g) < 1e-6 for g in groups):
            groups.append(val)
    sizes = []
    for g in groups:
        idx = [i for i, val in enumerate(w) if abs(val - g) < 1e-6]
        P = v[:, idx] @ v[:, idx].conj().T
        dimblock = len(orth([P @ b for b in alg], n))
        sizes.append(int(round(np.sqrt(dimblock))))
    return sorted(sizes), len(Z)


def haar(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
    return q * (np.diag(r) / abs(np.diag(r)))


def commute(A, B):
    return max(np.abs(a @ b - b @ a).max() for a in A for b in B)


def mat_units(n):
    out = []
    for i in range(n):
        for j in range(n):
            e = np.zeros((n, n), complex)
            e[i, j] = 1
            out.append(e)
    return out


def E1():
    # site = M_2 (x) M_3 ; Phi(A_h) = M_2 on L_h (x) M_3 on R_{h+1}, then site unitaries.
    d, cL, cR = 6, 2, 3
    U = [haar(d) for _ in range(3)]
    # region sites 0,1,2 with tensor factors L0 R0 L1 R1 L2 R2
    fdims = [cL, cR, cL, cR, cL, cR]

    def phi_site(h):
        gens = []
        for eL in mat_units(cL):
            for eR in mat_units(cR):
                ms = [np.eye(k) for k in fdims]
                ms[2 * h] = eL
                ms[2 * (h + 1) + 1] = eR
                gens.append(kron_all(ms))
        Ug = kron_all(U)
        return [Ug @ g @ Ug.conj().T for g in gens]

    dims = [d, d, d]
    X0 = orth(phi_site(0), d ** 3)
    X1 = orth(phi_site(1), d ** 3)
    print("E1 dim Phi(A_0) =", len(X0), "dim Phi(A_1) =", len(X1))
    print("E1 Phi(A_0), Phi(A_1) commute: err", commute(X0, X1))
    S00, S01, S02 = (support(X0, dims, s) for s in range(3))
    S11 = support(X1, dims, 1)
    for name, S in [("S(0,0)", S00), ("S(0,1)", S01), ("S(0,2)", S02), ("S(1,1)", S11)]:
        print("E1", name, "dim", len(S), "blocks", blocks(S, d))
    kmin = blocks(S00, d)[0][0] * blocks(S01, d)[0][0] * blocks(S02, d)[0][0]
    print("E1 k_min product over N-slots =", kmin, "(d =", d, ")")
    print("E1 site-1 supports commute: err", commute(S01, S11))
    gen1 = closure(orth([a @ b for a in S01 for b in S11], d), d)
    print("E1 site-1 supports generate dim", len(gen1), "of", d * d)
    # X0 lies in the tensor product of its supports (slice lemma), so equality is a
    # dimension count; also test membership of random elements via product projections.
    prod_dim = len(S00) * len(S01) * len(S02)
    P = [np.array([s.reshape(-1) for s in S]).T for S in (S00, S01, S02)]
    Pr = [p @ np.linalg.pinv(p) for p in P]
    x = sum(rng.normal() * b for b in X0)
    t = x.reshape([d] * 6).transpose(0, 3, 1, 4, 2, 5).reshape(d * d, d * d, d * d)
    t2 = np.einsum("ia,jb,kc,abc->ijk", Pr[0], Pr[1], Pr[2], t)
    print("E1 dim tensor of supports", prod_dim, "= dim Phi(A_0)", len(X0),
          "; membership residual", np.abs(t2 - t).max())


def E2():
    d = 2
    X = np.array([[0, 1], [1, 0]], complex)
    Zm = np.diag([1, -1]).astype(complex)
    I = np.eye(2)
    # sites -1,0,1,2 ; Phi(X_h) = Z_{h-1} X_h Z_{h+1}, Phi(Z_h) = Z_h
    def op(ms):
        return kron_all(ms)
    X0 = closure([op([Zm, X, Zm, I]), op([I, Zm, I, I])], 16)
    X1 = closure([op([I, Zm, X, Zm]), op([I, I, Zm, I])], 16)
    dims = [2, 2, 2, 2]
    print("E2 Phi(A_0), Phi(A_1) commute: err", commute(X0, X1))
    S00 = support(X0, dims, 1)
    S10 = support(X1, dims, 1)
    print("E2 site-0 support of Phi(A_0): dim", len(S00), "; of Phi(A_1): dim", len(S10))
    print("E2 these supports commute? err", commute(S00, S10), "(nonzero = teeth)")


def E3():
    n = 10
    B = []
    for e in mat_units(5):
        m = np.zeros((n, n), complex)
        m[:5, :5] = e
        B.append(m)
    m = np.zeros((n, n), complex)
    m[5:, 5:] = np.eye(5)
    B.append(m)
    B = closure(orth(B, n), n)
    Bc = []
    m = np.zeros((n, n), complex)
    m[:5, :5] = np.eye(5)
    Bc.append(m)
    for e in mat_units(5):
        m = np.zeros((n, n), complex)
        m[5:, 5:] = e
        Bc.append(m)
    Bc = closure(orth(Bc, n), n)
    bB, zB = blocks(B, n)
    bC, zC = blocks(Bc, n)
    print("E3 commute err", commute(B, Bc))
    print("E3 dim/centre product", (len(B) / zB) * (len(Bc) / zC), "vs d^2 =", n * n)
    print("E3 k_min product", bB[0] * bC[0], "vs d =", n)


def E4():
    # M_2 (x) M_2 = M_4 embedded unitally in S1 (x) S2 with S1 = M_2 (+) M_2 on C^4, S2 = M_2
    # x (x) y  ->  (x (+) u x u*) (x) y ; site dims 4 and 2
    u = haar(2)
    gens = []
    for ex in mat_units(2):
        for ey in mat_units(2):
            left = np.zeros((4, 4), complex)
            left[:2, :2] = ex
            left[2:, 2:] = u @ ex @ u.conj().T
            gens.append(np.kron(left, ey))
    Xa = orth(gens, 8)
    S1 = support(Xa, [4, 2], 0)
    S2 = support(Xa, [4, 2], 1)
    print("E4 dim image", len(Xa), "S1 blocks", blocks(S1, 4), "S2 blocks", blocks(S2, 2))
    print("E4 k_min product", blocks(S1, 4)[0][0] * blocks(S2, 2)[0][0], ">= d = 4")


if __name__ == "__main__":
    E1()
    E2()
    E3()
    E4()
