"""Symmetry-reduced Ozawa SDP for Gamma_3 (H = signed permutations of a,b,c, order 48).
max lam  s.t.  Delta^2 - lam*Delta = sum_{x,y in B_r} P_xy x^-1 y,  P = sum_rho sum_k U^(k) Q_rho U^(k)^T, Q_rho >= 0.
Usage: python3 sdp_sym.py QFILE r [clarabel|scs] [out.npz]"""
import sys, time, numpy as np, scipy.sparse as sp
from groupball import GroupBall
from wedderburn import irreps, adapted_bases

def delta_coeffs(G):
    S = [G.step(0, s) for s in range(6)]
    D1 = {0: 6.0}
    for s in S: D1[s] = D1.get(s, 0) - 1.0
    D2 = {}
    for g, cg in D1.items():
        for h, ch in D1.items():
            k = G.prod(g, h); D2[k] = D2.get(k, 0) + cg * ch
    return D1, D2

def build(qfile, r):
    t0 = time.time()
    G = GroupBall(qfile, 2 * r)
    B = sorted(G.B(r), key=lambda g: (G.dist[g], g)); n = len(B); loc = {g: i for i, g in enumerate(B)}
    B2 = G.B(2 * r)
    Hs, reps = irreps()
    imgs = [G.auto(p, s) for p, s in Hs]
    # automorphism check: img(g s) = img(g) sigma(s) on all edges inside B_{2r}
    for (p, sg), img in zip(Hs, imgs):
        for g in B2:
            if G.dist[g] >= 2 * r: continue
            for x in range(3):
                h = int(G.nbr[x][g]); y = p[x]
                t = int(G.nbr[y][img[g]]) if sg[x] == 1 else int(G.nbi[y][img[g]])
                assert img[h] == t, "not an automorphism"
    act = [np.array([loc[int(img[g])] for g in B]) for img in imgs]
    inv = [G.inv(g) for g in B]
    M = np.array([[G.prod(inv[i], B[j]) for j in range(n)] for i in range(n)])
    # orbits of H x <inversion> on B_{2r}
    orb = {}
    for g in B2:
        if g in orb: continue
        cl = set(int(img[g]) for img in imgs); cl |= set(G.inv(z) for z in cl)
        for z in cl: orb[z] = g
    D1, D2 = delta_coeffs(G)
    for z in D2: assert abs(D2[z] - D2.get(orb[z], 0)) < 1e-12
    orep = sorted(set(orb[z] for z in set(M.ravel().tolist()) | set(D2)))
    print(f"r={r}: n={n}, |B_2r|={len(B2)}, orbit rows={len(orep)} [{time.time()-t0:.1f}s]", flush=True)
    bases = adapted_bases(act, reps)
    print("  blocks (d,m):", [(d, U[0].shape[1]) for d, U in bases], flush=True)
    # pairs for representative g only
    flatM = M.ravel(); rowof = {g: i for i, g in enumerate(orep)}
    sel = np.array([z in rowof for z in flatM.tolist()])
    ids = np.nonzero(sel)[0]; I, J = ids // n, ids % n; R = np.array([rowof[z] for z in flatM[ids].tolist()])
    blocks = []
    for d, Us in bases:
        m = Us[0].shape[1]; C = np.zeros((len(orep), m, m))
        ch = max(1, int(2e7 // max(1, m * m)))
        for U in Us:
            for s in range(0, len(I), ch):
                X = U[I[s:s + ch]][:, :, None] * U[J[s:s + ch]][:, None, :]
                np.add.at(C, R[s:s + ch], X)
        C = (C + C.transpose(0, 2, 1)) / 2
        blocks.append((d, Us, C))
    d1 = np.array([D1.get(g, 0.0) for g in orep]); d2 = np.array([D2.get(g, 0.0) for g in orep])
    return dict(G=G, B=B, M=M, orep=orep, blocks=blocks, d1=d1, d2=d2, n=n)

def svec_idx(m):
    """upper triangle, column-major (Clarabel PSDTriangleConeT); SCS uses lower col-major = same entries (j,i)."""
    I, J = np.triu_indices(m); o = np.lexsort((I, J)); return I[o], J[o]

def solve(data, which='clarabel'):
    import clarabel
    nr = len(data['orep']); cols = [data['d1'].reshape(-1, 1)]; cones_psd = []
    for d, Us, C in data['blocks']:
        m = C.shape[1]
        if m == 0: continue
        I, J = svec_idx(m); sc = np.where(I == J, 1.0, np.sqrt(2.0))
        cols.append(C[:, I, J] * sc); cones_psd.append(m)
    Aeq = np.hstack(cols); nv = Aeq.shape[1] - 1
    A = sp.vstack([sp.csc_matrix(Aeq), sp.hstack([sp.csc_matrix((nv, 1)), -sp.identity(nv)])]).tocsc()
    b = np.concatenate([data['d2'], np.zeros(nv)]); c = np.zeros(nv + 1); c[0] = -1.0
    t0 = time.time()
    if which == 'clarabel':
        st = clarabel.DefaultSettings(); st.verbose = False; st.max_iter = 500
        st.tol_gap_abs = st.tol_gap_rel = st.tol_feas = 1e-10
        cones = [clarabel.ZeroConeT(nr)] + [clarabel.PSDTriangleConeT(m) for m in cones_psd]
        sol = clarabel.DefaultSolver(sp.csc_matrix((nv + 1, nv + 1)), c, A, b, cones, st).solve()
        x = np.array(sol.x); status = str(sol.status)
    else:
        import scs
        # SCS psd ordering = lower col-major; for symmetric matrices entries (i,j)->(j,i): reorder
        raise NotImplementedError
    print(f"  {which}: status={status} lam={x[0]:.6e} vars={nv} rows={nr} [{time.time()-t0:.1f}s]", flush=True)
    return x

if __name__ == '__main__':
    data = build(sys.argv[1], int(sys.argv[2]))
    x = solve(data, sys.argv[3] if len(sys.argv) > 3 else 'clarabel')
    if len(sys.argv) > 4: np.save(sys.argv[4], x)
