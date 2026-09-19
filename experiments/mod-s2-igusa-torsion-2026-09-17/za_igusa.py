#!/usr/bin/env python3
"""Exact H_1 and separating-twist census of the Igusa preimage, equivariantly.

G_I = pi^-1(Gamma(4,8)) <= K_4 = pi^-1(Gamma(4)) inside Pbar = PMod(S_{0,6}),
with A = K_4 / G_I = Gamma(4)/Gamma(4,8) = F_2^4 (elementary abelian).
The 16-sheeted cover X~ of the level-4 Reidemeister-Schreier presentation
complex X of K_4 is a presentation complex of G_I.  Its cellular chains are
free Z[A]-modules:  C_2 = Z[A]^rels -> C_1 = Z[A]^gens -> C_0 = Z[A], with
the Fox matrix over Z[A] (A-labels of the Schreier generators from
matrices mod 8).  We collapse (2-cell, 1-cell) pairs equivariantly, i.e.
eliminate a generator through a relator whose coefficient is a trivial unit
+-a (a in A); each such step is 16 elementary collapses of X~ and keeps
the homology.  The census only needs Q = C_1 / im d_2:
  * a separating-twist class of G_I is a 1-cycle b * z (b in A, z the lift
    of the traced twist square from the level-4 coset), and W = {w : sum
    w_i z_i in im d_2} is read off in Q;
  * Q = H_1(G_I) + d_1(C_1) and d_1(C_1) = augmentation ideal of Z[A] is
    free of rank 15, so Q = H_1(G_I) + Z^15: tors Q = tors H_1(G_I) and
    rank Q = b_1(G_I) + 15.

    python3 za_igusa.py build out.pkl        (trace + equivariant elimination)
    python3 za_igusa.py census out.pkl res.json
"""
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "..", "mod-s2-palindrome-transversal-relations-2026-09-17")
sys.path.insert(0, TOOL)
sys.path.insert(0, os.path.join(HERE, "..", "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import pure as P  # noqa: E402
import between48 as B48  # noqa: E402

NA = 16
XT = np.array([[a ^ c for a in range(NA)] for c in range(NA)])  # XT[c][a]


def zmul(f, g):
    """(f g)[c] = sum_a f[a] g[a ^ c] in Z[F_2^4]."""
    return g[XT] @ f


def zmono(s, b):
    e = np.zeros(NA, dtype=object)
    e[b] = s
    return e


def level4_cosets():
    """Level-4 cosets of Pbar (as in between48.enumerate_cosets with S =
    sp_4(F_2)), keeping the representative matrices mod 8."""
    S4 = [np.array(b) for b in B48.sp4_f2_basis()]
    mats = B48.pure_mats()
    canon = B48.make_canon(S4)
    I4 = np.eye(4, dtype=np.int64)
    index, reps, act, tree = {canon(I4): 0}, [I4], [], set()
    q = 0
    while q < len(reps):
        row = []
        for p, Bm in enumerate(mats):
            nb = (reps[q] @ Bm) % 8
            key = canon(nb)
            if key not in index:
                index[key] = len(reps)
                reps.append(nb)
                tree.add((q, p))
            row.append(index[key])
        act.append(row)
        q += 1
    assert act == B48.enumerate_cosets(S4)
    return act, reps, mats, tree


def a_labeller():
    """X (4x4 mod 2 with I + 4X in Gamma(4)/Gamma(8)) -> label in A = 0..15,
    a homomorphism sp_4(F_2) -> sp_4(F_2)/Alt."""
    Salt = [np.array(b) for b in B48.alt_subspace()]
    piv = [int(np.nonzero(b)[0][0]) for b in Salt]
    Ssp = [np.array(b) for b in B48.sp4_f2_basis()]

    def red(v):
        v = np.array(v) % 2
        for b, p in zip(Salt, piv):
            if v[p]:
                v = (v + b) % 2
        return int("".join(str(int(t)) for t in v), 2)

    vals = sorted({red(sum(c * b for c, b in zip(bits, Ssp)) % 2)
                   for bits in np.ndindex(*(2,) * len(Ssp))})
    assert len(vals) == NA
    basis = []                       # greedy F_2-basis of the reduced values
    span = {0}
    for v in vals:
        if v not in span:
            basis.append(v)
            span |= {s ^ v for s in span}
    assert len(basis) == 4 and len(span) == NA
    code = {}
    for bits in range(NA):
        v = 0
        for i in range(4):
            if bits >> i & 1:
                v ^= basis[i]
        code[v] = bits
    return lambda X: code[red(X.flatten())]


def sinv8(M):
    """Inverse of a symplectic matrix mod 8: M^-1 = -J M^T J."""
    J = C.J
    return (-J @ M.T @ J) % 8


def gen_labels(act, reps, mats, tree):
    lab = a_labeller()
    I4 = np.eye(4, dtype=np.int64)
    for M in reps + mats:
        assert ((sinv8(M) @ M) % 8 == I4).all()
    glab = {}
    for c, row in enumerate(act):
        for p, d in enumerate(row):
            Y = (reps[c] @ mats[p] @ sinv8(reps[d])) % 8
            if ((Y + I4) % 4 == 0).all():
                Y = (-Y) % 8
            assert ((Y - I4) % 4 == 0).all()
            X = ((Y - I4) % 8) // 4
            glab[(c, p)] = lab(X)
            if (c, p) in tree:
                assert glab[(c, p)] == 0 and (X == 0).all()
    return glab


def ztrace(act, gen, glab, word, c, vec):
    """Fox rewriting over Z[A]: the letter x_g read at A-value u adds
    delta_u to coordinate g (delta_(u + a_g), with sign -, for x_g^-1).
    Returns (end coset, end A-value)."""
    inv = B48.inverse_action(act)
    u = 0
    for a in word:
        p = abs(a) - 1
        if a > 0:
            d = act[c][p]
            g = gen.get((c, p))
            if g is not None:
                vec.setdefault(g, np.zeros(NA, dtype=object))[u] += 1
            u ^= glab[(c, p)]
        else:
            d = inv[c][p]
            u ^= glab[(d, p)]
            g = gen.get((d, p))
            if g is not None:
                vec.setdefault(g, np.zeros(NA, dtype=object))[u] -= 1
        c = d
    return c, u


def is_unit(f):
    nz = [i for i in range(NA) if f[i]]
    if len(nz) == 1 and f[nz[0]] in (1, -1):
        return int(f[nz[0]]), nz[0]
    return None


def build_rows():
    act, reps, mats, tree = level4_cosets()
    k = len(act)
    gen = B48.schreier(act)
    assert set(gen) == {(c, p) for c in range(k) for p in range(len(mats))} - tree
    glab = gen_labels(act, reps, mats, tree)
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(k):
            vec = {}
            assert ztrace(act, gen, glab, w, c, vec) == (c, 0)
            vec = {g: a for g, a in vec.items() if any(a)}
            if vec:
                rows.append(vec)
    TW = P.standard_twists(P.conj_table())
    vs, owner = [], []
    for ti, t in enumerate(P.TRIPLES):
        sq = TW[t] * 2
        for c in range(k):
            vec = {}
            assert ztrace(act, gen, glab, sq, c, vec) == (c, 0)
            vs.append({g: a for g, a in vec.items() if any(a)})
            owner.append((ti, c))
    labs = sorted(set(glab.values()))
    return k, gen, rows, vs, owner, labs


HAD = np.array([[(-1) ** bin(c & a).count("1") for a in range(NA)]
                for c in range(NA)], dtype=np.int64)
UNITS = {tuple(s * HAD[:, b]): (s, b) for s in (1, -1) for b in range(NA)}


def wht(f):
    """Walsh-Hadamard transform: the injective ring map Z[A] -> Z^16,
    f -> (chi(f))_chi; products become coordinatewise."""
    return HAD @ np.array([int(x) for x in f], dtype=np.int64)


def iwht(F):
    f = HAD @ F
    assert (f % NA == 0).all()
    return f // NA


def w_eliminate(rows, vs):
    """z_eliminate in Walsh-Hadamard coordinates (int64, vectorised)."""
    t0 = time.time()
    rows = {r: {g: wht(f) for g, f in v.items()} for r, v in enumerate(rows)}
    vs = [{g: wht(f) for g, f in v.items()} for v in vs]
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    vcol = {}
    for t, v in enumerate(vs):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    eliminated, big = 0, 0
    progress = True
    while progress:
        progress = False
        for r in sorted(rows, key=lambda r: len(rows[r])):
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if tuple(a) in UNITS]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            e = v[j]                       # unit, e * e = 1
            piv = v
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            for store, index, targets in ((rows, colrows, list(colrows.get(j, ()))),
                                          (vs, vcol, list(vcol.get(j, ())))):
                for q in targets:
                    row = store[q]
                    fe = row[j] * e
                    for g, pg in piv.items():
                        nv = (row[g] if g in row else 0) - fe * pg
                        if nv.any():
                            if g not in row:
                                index.setdefault(g, set()).add(q)
                            row[g] = nv
                            big = max(big, int(np.abs(nv).max()))
                        elif g in row:
                            del row[g]
                            index[g].discard(q)
                    assert j not in row
            colrows.pop(j, None)
            vcol.pop(j, None)
            eliminated += 1
            progress = True
            if eliminated % 500 == 0:
                print(f"  eliminated {eliminated}, rows {len(rows)}, "
                      f"max |wht| {big} [{time.time()-t0:.1f}s]", flush=True)
    assert big < 2 ** 50
    R = [{g: iwht(F) for g, F in v.items()} for v in rows.values() if v]
    V = [{g: iwht(F) for g, F in v.items()} for v in vs]
    cols = sorted({g for v in R for g in v} | {g for v in V for g in v})
    return cols, R, V, eliminated


MOD_M = 8
MODN = 1 << MOD_M


def rinv(u):
    """Inverse in (Z/2^m)[A] of u with odd augmentation (u^2 = 1 mod 2
    because A has exponent 2), by Newton iteration y <- y (2 - u y)."""
    y = u % MODN
    for _ in range(MOD_M.bit_length() + 1):
        y = zmul(y, (2 * np.eye(1, NA, 0, dtype=np.int64)[0] - zmul(u, y)) % MODN) % MODN
    assert (zmul(u, y) % MODN == np.eye(1, NA, 0, dtype=np.int64)[0]).all()
    return y


MUNITS = {tuple(int(x) for x in (s * np.eye(NA, dtype=np.int64)[b]) % MODN)
          for s in (1, -1) for b in range(NA)}   # +-delta_b mod 2^m


def m_eliminate(rows, vs, max_cost=None):
    """Elimination over the local ring (Z/2^m)[A]: every entry of odd
    augmentation is a unit.  Keeps Q (x) Z/2^m = coker over Z/2^m.
    With max_cost, only trivial-unit pivots whose update touches at most
    max_cost (row, entry) pairs are used (the cheap sparse phase)."""
    t0 = time.time()
    rows = {r: {g: np.array([int(x) for x in f], dtype=np.int64) % MODN
                for g, f in v.items()} for r, v in enumerate(rows)}
    vs = [{g: np.array([int(x) for x in f], dtype=np.int64) % MODN
           for g, f in v.items()} for v in vs]
    for store in (rows.values(), vs):
        for v in store:
            for g in [g for g, f in v.items() if not f.any()]:
                del v[g]
    colrows, vcol = {}, {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    for t, v in enumerate(vs):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    eliminated = 0
    progress = True
    while progress:
        progress = False
        for r in sorted(rows, key=lambda r: len(rows[r])):
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if int(a.sum()) % 2]
            if max_cost is not None:
                units = [g for g in units if tuple(v[g]) in MUNITS and
                         len(v) * (len(colrows.get(g, ())) +
                                   len(vcol.get(g, ()))) <= max_cost]
            if not units:
                continue
            j = min(units, key=lambda g: (tuple(v[g]) not in MUNITS,
                                          len(colrows.get(g, ()))))
            e = rinv(v[j])
            piv = v
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            for store, index, targets in ((rows, colrows, list(colrows.get(j, ()))),
                                          (vs, vcol, list(vcol.get(j, ())))):
                for q in targets:
                    row = store[q]
                    fe = zmul(row[j], e) % MODN
                    for g, pg in piv.items():
                        nv = ((row[g] if g in row else 0) - zmul(fe, pg)) % MODN
                        if nv.any():
                            if g not in row:
                                index.setdefault(g, set()).add(q)
                            row[g] = nv
                        elif g in row:
                            del row[g]
                            index[g].discard(q)
                    assert j not in row
            colrows.pop(j, None)
            vcol.pop(j, None)
            eliminated += 1
            progress = True
            if eliminated % 500 == 0:
                print(f"  eliminated {eliminated}, rows {len(rows)} "
                      f"[{time.time()-t0:.1f}s]", flush=True)
    R = [v for v in rows.values() if v]
    cols = sorted({g for v in R for g in v} | {g for v in vs for g in v})
    return cols, R, vs, eliminated


def dense_eliminate(cols, R, V):
    """Dense phase over (Z/2^m)[A]: pivot on any unit (odd augmentation)
    until none is left.  Arrays are float32 with entries in [0, 2^m); every
    update F @ P has |terms| < 16 * 2^(2m) < 2^24, so it is exact."""
    t0 = time.time()
    assert 16 * MODN * MODN < 2 ** 24
    pos = {g: i for i, g in enumerate(cols)}
    n1 = len(cols)

    def dense(rows):
        D = np.zeros((len(rows), n1, NA), dtype=np.float32)
        for i, v in enumerate(rows):
            for g, f in v.items():
                D[i, pos[g]] = f % MODN
        return D
    DR, DV = dense(R), dense(V)
    alive_cols = list(range(n1))
    npiv = 0
    while True:
        if len(DR) == 0:
            break
        aug = DR.sum(axis=2).astype(np.int64) % 2           # rows x cols
        if not aug.any():
            break
        nnz = (DR.any(axis=2)).sum(axis=1)
        cand = np.nonzero(aug.any(axis=1))[0]
        r = int(cand[np.argmin(nnz[cand])])
        j = int(np.nonzero(aug[r])[0][0])
        e = rinv(DR[r, j].astype(np.int64))
        prow = (DR[r].astype(np.int64)[:, XT] @ e) % MODN    # (cols, 16)
        assert (prow[j] == np.eye(1, NA, 0, dtype=np.int64)[0]).all()
        P = prow[:, XT].transpose(2, 0, 1).reshape(NA, -1).astype(np.float32)
        for D in (DR, DV):                  # row r itself becomes 0
            if len(D):
                F = D[:, j, :].copy()
                assert D.flags["C_CONTIGUOUS"]
                D2 = D.reshape(len(D), -1)
                assert np.shares_memory(D, D2)
                D2 -= F @ P
                np.mod(D2, MODN, out=D2)
                if D[:, j, :].any():
                    bad = np.nonzero(D[:, j, :].any(axis=1))[0]
                    print("DEBUG", D.flags["C_CONTIGUOUS"], np.shares_memory(D, D2),
                          len(bad), bad[:5], D[bad[0], j], F[bad[0]],
                          D.dtype, D.shape, flush=True)
                    raise AssertionError
        assert not DR[r].any()
        npiv += 1
        if npiv % 25 == 0:
            keep = [c for c in range(DR.shape[1])
                    if DR[:, c].any() or DV[:, c].any()]
            DR, DV = DR[:, keep], DV[:, keep]
            alive_cols = [alive_cols[c] for c in keep]
            nz = DR.any(axis=(1, 2))
            # fancy indexing may return a non-C-contiguous array, and then
            # reshape copies and the in-place update would be lost
            DR = np.ascontiguousarray(DR[nz])
            DV = np.ascontiguousarray(DV)
            print(f"  dense pivots {npiv}, cols {len(alive_cols)}, rows "
                  f"{len(DR)} [{time.time()-t0:.1f}s]", flush=True)
    keep = [c for c in range(DR.shape[1]) if DR[:, c].any() or DV[:, c].any()]
    DR, DV = DR[:, keep], DV[:, keep]
    alive_cols = [alive_cols[c] for c in keep]
    DR = DR[DR.any(axis=(1, 2))]
    newcols = [cols[c] for c in alive_cols]

    def back(D):
        out = []
        for row in D.astype(np.int64):
            out.append({newcols[c]: row[c] for c in range(len(newcols))
                        if row[c].any()})
        return out
    return newcols, back(DR), back(DV), npiv


def build_mod(out):
    t0 = time.time()
    sp = out + ".sparse"
    if os.path.exists(sp):
        with open(sp, "rb") as f:
            k, owner, cols, R, V, ne = pickle.load(f)
    else:
        k, gen, rows, vs, owner, labs = build_rows()
        cols, R, V, ne = m_eliminate(rows, vs, max_cost=300000)
        with open(sp, "wb") as f:
            pickle.dump((k, owner, cols, R, V, ne), f)
    print(f"mod 2^{MOD_M} sparse: eliminated {ne}, Z[A]-cols {len(cols)}, "
          f"rows {len(R)} [{time.time()-t0:.1f}s]", flush=True)
    cols, R, V, nd = dense_eliminate(cols, R, V)
    ne += nd
    print(f"mod 2^{MOD_M}: eliminated {ne}, surviving Z[A]-cols {len(cols)}, "
          f"rows {len(R)} [{time.time()-t0:.1f}s]", flush=True)
    with open(out, "wb") as f:
        pickle.dump({"cols": cols, "R": R, "V": V, "owner": owner, "k": k,
                     "m": MOD_M}, f)


def val2(x):
    x = int(x) % MODN
    return MOD_M if x == 0 else (x & -x).bit_length() - 1


def smith_mod(G):
    """Smith form over Z/2^m of the row module of G (numpy int64, entries
    mod 2^m).  Row operations are free; column operations are recorded in
    the unimodular Ccol.  Returns (vals, Ccol) with rowspace(G) Ccol =
    sum_i 2^vals[i] Z/2^m e_i  (vals[i] = m means the i-th summand is free
    of the relations, i.e. contributes Z/2^m)."""
    G = G.copy() % MODN
    nr, N = G.shape
    Ccol = np.eye(N, dtype=np.int64)
    vals = [MOD_M] * N
    r = 0
    for t in range(N):
        if r >= nr:
            break
        sub = G[r:, t:]
        nzmask = sub != 0
        if not nzmask.any():
            break
        v = np.full(sub.shape, MOD_M)
        for b in range(MOD_M - 1, -1, -1):
            v[(sub % (1 << (b + 1)) == (1 << b))] = b
        i, j = np.unravel_index(int(np.argmin(v)), v.shape)
        vmin = int(v[i, j])
        i += r
        j += t
        G[[r, i]] = G[[i, r]]
        G[:, [t, j]] = G[:, [j, t]]
        Ccol[:, [t, j]] = Ccol[:, [j, t]]
        p = int(G[r, t])
        u = p >> vmin                         # odd
        uinv = pow(u, -1, MODN)
        G[r] = (G[r] * uinv) % MODN            # pivot = 2^vmin
        # clear column t below/above (row ops)
        col = G[:, t].copy()
        col[r] = 0
        f = (col >> vmin) % MODN
        G = (G - np.outer(f, G[r])) % MODN
        # clear row r to the right (column ops)
        rowv = G[r].copy()
        rowv[t] = 0
        g = (rowv >> vmin) % MODN
        G = (G - np.outer(G[:, t], g)) % MODN
        Ccol = (Ccol - np.outer(Ccol[:, t], g)) % MODN
        vals[t] = vmin
        r += 1
    return vals, Ccol


def expand_mod(v, pos, b):
    out = np.zeros(NA * len(pos), dtype=np.int64)
    for g, f in v.items():
        out[NA * pos[g]:NA * pos[g] + NA] = f[XT[b]]
    return out % MODN


def census_mod(pkl, l4pkl, out):
    """Q (x) Z/2^m, the classes (level-4 class, torsion coordinate), W."""
    import json
    t0 = time.time()
    rng = np.random.default_rng(20260919)
    d = pickle.load(open(pkl, "rb"))
    l4 = pickle.load(open(l4pkl, "rb"))
    cols, R, V, owner = d["cols"], d["R"], d["V"], d["owner"]
    assert d["m"] == MOD_M and l4["owner"] == owner
    pos = {g: i for i, g in enumerate(cols)}
    N = NA * len(cols)
    def chunks(size=256):
        for i in range(0, len(R), size):
            yield np.array([expand_mod(v, pos, b) for v in R[i:i + size]
                            for b in range(NA)], dtype=np.int64).reshape(-1, N)
    nE = NA * len(R)
    print(f"census_mod: N {N}, expanded rows {nE} [{time.time()-t0:.1f}s]",
          flush=True)
    if nE > 2 * N + 64:            # random 0/1 mixing, exact in float64
        s = N + 64
        G = np.zeros((s, N))
        for ch in chunks():
            G = np.mod(G + rng.integers(0, 2, (s, len(ch))).astype(np.float64)
                       @ ch.astype(np.float64), MODN)
        G = G.astype(np.int64)
    else:
        G = np.vstack(list(chunks())) if nE else np.zeros((0, N), dtype=np.int64)
    vals, Ccol = smith_mod(G)
    # verification: every relator row lies in the module found, so the
    # random mixing lost nothing and the Smith form is that of Q (x) Z/2^m
    for ch in chunks():
        img = (ch @ Ccol) % MODN
        for t, v in enumerate(vals):
            assert (img[:, t] % (1 << v) == 0).all(), "mixing lost relations"
    res_verified = True
    free = sum(1 for v in vals if v == MOD_M)
    tors = sorted(1 << v for v in vals if 0 < v < MOD_M)
    res = {"level4_cosets": d["k"], "m": MOD_M, "zA_cols": len(cols),
           "zA_rows": len(R), "Q_mod_2m_free_summands": free,
           "Q_mod_2m_torsion": tors, "b1_if_rank_Q_is_free": free - 15,
           "all_relator_rows_verified_in_mixed_module": res_verified}
    print(json.dumps(res), f"[{time.time()-t0:.1f}s]", flush=True)
    keep = [t for t, v in enumerate(vals) if v > 0]
    mods = [1 << vals[t] for t in keep]
    keys, over = [], []
    for i, v in enumerate(V):
        for b in range(NA):
            y = (expand_mod(v, pos, b) @ Ccol) % MODN
            keys.append((l4["lab"][i],
                         tuple(int(y[t]) % mm for t, mm in zip(keep, mods))))
            over.append(i)
    distinct = sorted(set(keys))
    res["classes"] = len(distinct)
    fib = {}
    for kk in distinct:
        fib.setdefault(kk[0], []).append(kk)
    res["level4_classes"] = len(fib)
    res["fibre_sizes"] = sorted({len(x) for x in fib.values()})
    # torsion coordinates that actually vary between classes
    tt = [j for j, mm in enumerate(mods) if mm < MODN]
    res["torsion_coordinate_values"] = sorted({tuple(kk[1][j] for j in tt)
                                               for kk in distinct})
    print(json.dumps(res), f"[{time.time()-t0:.1f}s]", flush=True)
    n4 = l4["n4"]
    Rbig = [list(r) + [0] * len(keep) for r in l4["H"]]
    for j, mm in enumerate(mods):
        e = [0] * (n4 + len(keep))
        e[n4 + j] = mm
        Rbig.append(e)
    Vbig = [list(l4["distinct"][kk[0]]) + list(kk[1]) for kk in distinct]
    B = C.w_lattice(Rbig, Vbig, n4 + len(keep))
    res["W_rank"] = len(B)
    print(f"W rank {len(B)} [{time.time()-t0:.1f}s]", flush=True)
    json.dump(res, open(out, "w"), indent=1)
    pickle.dump({"B": B, "distinct": distinct, "keys": keys, "over": over},
                open(out + ".pkl", "wb"))


def milp_stage(resfile, out):
    """Exact d, best signed l1 certificate, positive minima of W."""
    import json
    t0 = time.time()
    res = json.load(open(resfile))
    B = pickle.load(open(resfile + ".pkl", "rb"))["B"]
    dev, h = C.distance_milp(B)
    res["d"] = str(dev)
    res["optimal_character_h"] = h
    print(f"d = {dev} [{time.time()-t0:.1f}s]", flush=True)
    l1, w = C.best_certificate(B)
    res["best_l1_certificate"] = l1
    res["best_l1_certificate_support"] = {str(j): x for j, x in enumerate(w) if x}
    print(f"best l1 certificate {l1} [{time.time()-t0:.1f}s]", flush=True)
    for r in (1, 2):
        a, wp = B48.positive_min(B, r)
        res[f"positive_min_aug_{r}_mod_3"] = a
        if wp is not None:
            res[f"positive_min_aug_{r}_support"] = {
                str(j): x for j, x in enumerate(wp) if x}
        print(f"positive min (aug {r} mod 3) = {a} [{time.time()-t0:.1f}s]",
              flush=True)
    json.dump(res, open(out, "w"), indent=1)


def z_eliminate(rows, vs):
    """Equivariant unit elimination (cf. census.unit_eliminate over Z)."""
    rows = dict(enumerate(rows))
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    vcol = {}
    for t, v in enumerate(vs):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    eliminated = 0
    progress = True
    while progress:
        progress = False
        for r in sorted(rows, key=lambda r: len(rows[r])):
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if is_unit(a)]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            s, b = is_unit(v[j])
            piv = v
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            # x_j = -(s delta_b) sum_{g != j} piv_g x_g ; target row q:
            # q <- q - q_j (s delta_b) piv
            for store, index, targets in ((rows, colrows, list(colrows.get(j, ()))),
                                          (vs, vcol, list(vcol.get(j, ())))):
                for q in targets:
                    row = store[q]
                    f = row[j]
                    fe = s * f[XT[b]]            # f * (s delta_b)
                    for g, pg in piv.items():
                        nv = row.get(g, 0) - zmul(fe, pg) if g in row else -zmul(fe, pg)
                        if any(nv):
                            if g not in row:
                                index.setdefault(g, set()).add(q)
                            row[g] = nv
                        elif g in row:
                            del row[g]
                            index[g].discard(q)
                    assert j not in row
            colrows.pop(j, None)
            vcol.pop(j, None)
            eliminated += 1
            progress = True
    cols = sorted({g for v in rows.values() for g in v} |
                  {g for v in vs for g in v})
    return cols, [v for v in rows.values() if v], vs, eliminated


def expand(v, pos, b):
    """Integer coordinates of delta_b * v (v a Z[A]-row)."""
    out = [0] * (NA * len(pos))
    for g, f in v.items():
        fb = f[XT[b]]
        base = NA * pos[g]
        for a in range(NA):
            if fb[a]:
                out[base + a] = int(fb[a])
    return out


def build(out):
    t0 = time.time()
    k, gen, rows, vs, owner, labs = build_rows()
    print(f"level-4 cosets {k}, gens {len(gen)}, Z[A]-relators {len(rows)}, "
          f"generator labels hit {len(labs)} of 16 [{time.time()-t0:.1f}s]",
          flush=True)
    cols, R, V, ne = w_eliminate(rows, vs)
    mx = max((abs(int(x)) for v in R + V for f in v.values() for x in f),
             default=0)
    print(f"eliminated {ne}, surviving Z[A]-cols {len(cols)}, rows {len(R)}, "
          f"max |coef| {mx} [{time.time()-t0:.1f}s]", flush=True)
    with open(out, "wb") as f:
        pickle.dump({"cols": cols, "R": R, "V": V, "owner": owner, "k": k},
                    f)


def census(pkl, out, l4pkl=None):
    import json
    t0 = time.time()
    d = pickle.load(open(pkl, "rb"))
    cols, R, V, owner, k = d["cols"], d["R"], d["V"], d["owner"], d["k"]
    pos = {g: i for i, g in enumerate(cols)}
    n = NA * len(cols)
    Rint = sorted({tuple(expand(v, pos, b)) for v in R for b in range(NA)})
    print(f"census: integer cols {n}, distinct rows {len(Rint)}", flush=True)
    H = []
    for i in range(0, len(Rint), 3000):
        H = C.hnf_rows(H + [list(r) for r in Rint[i:i + 3000]], n)
    rank, tors = C.h1_invariants(H, n)
    res = {"level4_cosets": k, "zA_cols": len(cols), "zA_rows": len(R),
           "rank_Q": rank, "b1": rank - 15, "torsion": tors}
    print(f"Q = Z^{rank} + {tors}; b_1 = {rank - 15} [{time.time()-t0:.1f}s]",
          flush=True)
    keys, over = [], []
    for i, v in enumerate(V):
        for b in range(NA):
            keys.append(C.reduce_mod_hnf(expand(v, pos, b), H))
            over.append(i)
    distinct = sorted(set(keys))
    kidx = {kk: i for i, kk in enumerate(distinct)}
    lab = [kidx[kk] for kk in keys]
    res["classes"] = len(distinct)
    if l4pkl:
        l4 = pickle.load(open(l4pkl, "rb"))
        assert l4["owner"] == owner
        down = {}
        for c, i in zip(lab, over):
            assert down.setdefault(c, l4["lab"][i]) == l4["lab"][i]
        fib = {}
        for a, b in down.items():
            fib.setdefault(b, []).append(a)
        res["level4_classes"] = len(fib)
        res["fibre_sizes"] = sorted({len(x) for x in fib.values()})
    print(json.dumps(res), flush=True)
    B = C.w_lattice(H, [list(x) for x in distinct], n)
    res["W_rank"] = len(B)
    print(f"W rank {len(B)} [{time.time()-t0:.1f}s]", flush=True)
    json.dump(res, open(out, "w"), indent=1)
    pickle.dump({"B": B, "lab": lab, "over": over}, open(out + ".pkl", "wb"))


if __name__ == "__main__":
    if sys.argv[1] == "build":
        build(sys.argv[2])
    elif sys.argv[1] == "build_mod":
        build_mod(sys.argv[2])
    elif sys.argv[1] == "census_mod":
        census_mod(sys.argv[2], sys.argv[3], sys.argv[4])
    elif sys.argv[1] == "milp":
        milp_stage(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "census":
        census(sys.argv[2], sys.argv[3],
               sys.argv[4] if len(sys.argv) > 4 else None)
