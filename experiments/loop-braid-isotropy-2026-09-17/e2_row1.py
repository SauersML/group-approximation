"""Row q = 1 of the P-isotropy spectral sequence of the loop braid descending-link complexes.

Setting (artifact zp-loop-braid-isotropy-spectral-sequence-2026-09-17.md):
- Q = OM(G) is the strict fundamental domain, for a graph G on the ring set [n].
  Y-mode: G = K_{[n] - {v,w} - F} plus the single edge {v, w}.  X-mode: G = K_{[n] - F}.
- W = H_1(PLB_n; F_p) = F_p^{n(n-1)}, with basis e_ij (i != j).
- U_sigma = image of H_1(P_sigma) = functions constant on the blocks of the matching of sigma
  and zero on the diagonal blocks.  U_sigma = intersection of U_e over the edges e of sigma.
- Cech resolution: 0 -> W/U_sigma -> (+)_{e in sigma} W/U_e -> (+)_{e<f in sigma} M_ef -> 0,
  where M_ef = W/(U_e + U_f) is 2-dimensional, with coordinates lambda_1, lambda_2 below.

Write A = W/U, B = (+)_e W/U_e, C = (+)_{e<f} M_ef for the three coefficient systems. Then
  H_k(Q; B) = (+)_{u vertex}   W/U_{e(u)} (x) H~_{k-1}(lk u),
  H_k(Q; C) = (+)_{tau edge}   M_{e f}   (x) H~_{k-2}(lk tau),
and this script computes coker( H_{d+1}(Q; B) -> H_{d+1}(Q; C) ).  When H_d(Q; B) = 0 it
equals H_d(Q; A).  When moreover H_d(Q) = H_{d+1}(Q) = 0, it also equals H_{d-1}(Q; U), which
is E^2_{d-1,1} of the isotropy spectral sequence.

Usage: python3 e2_row1.py MODE n |F| d p
"""
import itertools
import sys

import flint


def flag_simplices(verts):
    """All simplices (sorted tuples) of OM on the given sorted vertex list, including ()."""
    verts = sorted(verts)
    out = [()]
    def rec(start, cur, used):
        for i in range(start, len(verts)):
            a, b = verts[i]
            if a in used or b in used:
                continue
            s = cur + (verts[i],)
            out.append(s)
            rec(i + 1, s, used | {a, b})
    rec(0, (), frozenset())
    return out


def by_dim(simps):
    D = {}
    for s in simps:
        D.setdefault(len(s) - 1, []).append(s)
    return D


def bd_matrix(D, d, p):
    """Augmented boundary C_d -> C_{d-1} as an nmod_mat of shape (|C_{d-1}|, |C_d|)."""
    rows = D.get(d - 1, [])
    cols = D.get(d, [])
    idx = {s: i for i, s in enumerate(rows)}
    M = flint.nmod_mat(max(len(rows), 1), max(len(cols), 1), p)
    if not rows or not cols:
        return M, 0 if not rows else len(rows), len(cols)
    for c, s in enumerate(cols):
        for i in range(len(s)):
            M[idx[s[:i] + s[i + 1:]], c] = (-1) ** i % p
    return M, len(rows), len(cols)


def cycles(D, d, p):
    """Basis of reduced cycles Z~_d as a list of dicts {simplex: coef}."""
    cols = D.get(d, [])
    if not cols:
        return []
    M, nr, nc = bd_matrix(D, d, p)
    X, nul = M.nullspace()
    out = []
    for j in range(nul):
        z = {}
        for i in range(nc):
            c = int(X[i, j])
            if c:
                z[cols[i]] = c
        out.append(z)
    return out


def cohomology_basis(D, d, p):
    """Cocycles phi_1..phi_h (lists over D[d]) whose classes form a basis of H~^d."""
    cols = D.get(d, [])
    if not cols:
        return []
    n_d = len(cols)
    # cocycles: phi with phi o bd_{d+1} = 0
    if D.get(d + 1):
        M, nr, nc = bd_matrix(D, d + 1, p)       # shape (n_d, n_{d+1})
        Mt = M.transpose()
        X, nul = Mt.nullspace()
        cocyc = [[int(X[i, j]) for i in range(n_d)] for j in range(nul)]
    else:
        cocyc = [[1 if i == j else 0 for i in range(n_d)] for j in range(n_d)]
    # coboundaries: rows of bd_d (phi = psi o bd_d); for d = 0 this is the constants
    M, nr, nc = bd_matrix(D, d, p)               # shape (n_{d-1}, n_d)
    cob = [[int(M[i, j]) for j in range(n_d)] for i in range(nr)]
    base = [r for r in cob if any(r)]
    def rank(rows):
        if not rows:
            return 0
        A = flint.nmod_mat(len(rows), n_d, p)
        for i, r in enumerate(rows):
            for j, x in enumerate(r):
                if x:
                    A[i, j] = x
        return A.rank()
    r0 = rank(base)
    chosen = []
    cur = base[:]
    for phi in cocyc:
        if rank(cur + [phi]) > r0 + len(chosen):
            chosen.append(phi)
            cur.append(phi)
    return chosen


def main(mode, n, nf, d, p):
    F = list(range(n - nf, n))
    free = [r for r in range(n) if r not in F]
    v, w = free[0], free[1]
    if mode == 'Y':
        kpart = [r for r in free if r not in (v, w)]
        edges = [tuple(sorted(e)) for e in itertools.combinations(kpart, 2)] + [(v, w)]
    else:
        edges = [tuple(sorted(e)) for e in itertools.combinations(free, 2)]
    edges = sorted(edges)
    eidx = {e: i for i, e in enumerate(edges)}
    Qverts = sorted([(a, b) for (a, b) in edges] + [(b, a) for (a, b) in edges])
    und = lambda u: tuple(sorted(u))

    def lk_verts(tau):
        used = set(x for u in tau for x in u)
        return [u for u in Qverts if u[0] not in used and u[1] not in used]

    Wbasis = [(i, j) for i in range(n) for j in range(n) if i != j]

    def lam(e, f, y):
        """lambda_1, lambda_2 of M_ef (e < f fixed) evaluated on the basis vector e_y."""
        (a, b), (c, dd) = e, f
        l1 = {(a, c): 1, (b, c): -1, (a, dd): -1, (b, dd): 1}
        l2 = {(c, a): 1, (c, b): -1, (dd, a): -1, (dd, b): 1}
        return (l1.get(y, 0), l2.get(y, 0))

    # cohomology of edge links, cached by vertex set
    coh_cache = {}
    def coh(tau):
        key = tuple(lk_verts(tau))
        if key not in coh_cache:
            D = by_dim(flag_simplices(list(key)))
            coh_cache[key] = (D, cohomology_basis(D, d - 1, p))
        return coh_cache[key]

    taus = []
    tcoord = {}
    for t in itertools.combinations(Qverts, 2):
        u1, u2 = t
        if set(u1) & set(u2):
            continue
        D, phis = coh(t)
        if not phis:
            continue
        e, f = sorted([und(u1), und(u2)])
        for j in range(2):
            for h in range(len(phis)):
                tcoord[(t, j, h)] = len(tcoord)
        taus.append(t)
    target_dim = len(tcoord)
    print(f"mode={mode} n={n} |F|={nf} d={d} p={p}: target H_{d+1}(Q;C) dim = {target_dim}",
          flush=True)

    HB = 0
    vecs = []
    for u in Qverts:
        L = lk_verts((u,))
        D = by_dim(flag_simplices(L))
        # dimension of H~_{d-1}(lk u), for the H_d(Q;B) = 0 check
        hb = len(cohomology_basis(D, d - 1, p)) if d - 1 >= -1 else 0
        HB += hb * (2 * n - 2)
        Z = cycles(D, d, p)
        if not Z:
            continue
        e = und(u)
        # residue of the Q-chain u*z at each tau = {u, u'}
        rows = []   # each row: dict (t, h) -> value, for one cycle
        for z in Z:
            res = {}
            for rho, c in z.items():
                sigma = tuple(sorted(rho + (u,)))
                sgn_u = (-1) ** sigma.index(u)
                for u2 in rho:
                    t = tuple(sorted((u, u2)))
                    if (t, 0, 0) not in tcoord:
                        continue
                    i, j = sigma.index(t[0]), sigma.index(t[1])
                    rest = tuple(x for x in sigma if x not in t)
                    s = sgn_u * (-1) ** (i + j) * c
                    res.setdefault(t, {})
                    res[t][rest] = (res[t].get(rest, 0) + s) % p
            ev = {}
            for t, chain in res.items():
                Dt, phis = coh(t)
                pos = {sm: k for k, sm in enumerate(Dt[d - 1])}
                for h, phi in enumerate(phis):
                    val = sum(cf * phi[pos[sm]] for sm, cf in chain.items()) % p
                    if val:
                        ev[(t, h)] = val
            if ev:
                rows.append(ev)
        if not rows:
            continue
        # reduce rows to a basis of R_u(Z)
        keys = sorted(set(k for r in rows for k in r))
        kidx = {k: i for i, k in enumerate(keys)}
        A = flint.nmod_mat(len(rows), len(keys), p)
        for i, r in enumerate(rows):
            for k, x in r.items():
                A[i, kidx[k]] = x
        A = A.rref()[0]
        rk = A.rank()
        for i in range(rk):
            ev = {keys[j]: int(A[i, j]) for j in range(len(keys)) if int(A[i, j])}
            for y in Wbasis:
                vec = {}
                for (t, h), x in ev.items():
                    f = und(t[0]) if t[1] == u else und(t[1])
                    ee, ff = sorted([e, f])
                    eps = 1 if e == ee else -1
                    l = lam(ee, ff, y)
                    for j in range(2):
                        if l[j]:
                            col = tcoord[(t, j, h)]
                            vec[col] = (vec.get(col, 0) + eps * l[j] * x) % p
                if vec:
                    vecs.append(vec)
    if vecs and target_dim:
        M = flint.nmod_mat(len(vecs), target_dim, p)
        for i, vec in enumerate(vecs):
            for c, x in vec.items():
                M[i, c] = x
        r = M.rank()
    else:
        r = 0
    print(f"  dim H_{d}(Q;B) = {HB}; rank of H_{d+1}(B)->H_{d+1}(C) = {r}; "
          f"coker dim = {target_dim - r}", flush=True)


if __name__ == '__main__':
    mode, n, nf, d, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    main(mode, n, nf, d, p)
