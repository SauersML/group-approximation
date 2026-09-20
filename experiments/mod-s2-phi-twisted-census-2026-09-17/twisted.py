#!/usr/bin/env python3
"""Z/3-equivariant (Shapiro) chains for the index-3 steps below Gamma_Phi.

Phi = Phi(U) = (Z/3)^2 is the Frattini subgroup of the 3-Sylow U of
Sp_4(F_3) (sylow.py).  For an order-3 subgroup L < Phi put
    Gamma_L = { A = I mod 2, A mod 3 in L },   M_L = pi^-1(Gamma_L).
Gamma_L is normal in Gamma_Phi with quotient Phi/L = Z/3, so M_L\\Pbar is a
regular Z/3-cover of the 2880 cosets M_Phi\\Pbar (Pbar = PMod(S_{0,6}), as in
pbar.py).  The cover is the derived graph of a voltage assignment:

  * base cosets c with BFS representatives X_c (mod-3 matrices, products of
    the pure generator matrices along the BFS tree, which is the Schreier
    tree of pbar.schreier);
  * for an edge c --p--> d the Schreier generator t_c x_p t_d^-1 of M_Phi has
    matrix g = X_c B_p X_d^-1 in +-Phi, and its voltage is phi_L(g) in Z/3,
    where phi_L : +-Phi -> Phi/L = Z/3 (tree edges have g = I, voltage 0).

The cellular chains of the cover are free over R = Z[t]/(t^3 - 1).  After
contracting the three lifts of the base tree, C_1 = R^{Schreier gens}, and
a relator traced from c has Fox row sum_edges (+-) t^sigma e_edge, sigma
being the current sheet.  Q = C_1 / (relator rows) is H_1(M_L) + I_R as an
abelian group (I_R = augmentation ideal = Z^2, the image of d_1), and

    Q (x)_R Z[omega]  = H_1(M_Phi; Z[omega]_chi) + Z[omega]      (chi(t) = omega)
    Q (x)_R Z         = H_1(M_Phi; Z)                            (t = 1).

Twist loops: for each base coset c and each of the 10 triples, the loop of
g_c T_A^2 g_c^-1 is closed in the base and in the cover (T_A^2 is Torelli);
its R-row z_{c,A} gives the classes t^s z_{c,A}, s = 0, 1, 2, of the three
lifts, i.e. the separating-twist classes of H_1(M_L).
"""
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pbar  # noqa: E402
import sylow as S  # noqa: E402

P = pbar.P


def log(*a):
    print(f"[{time.strftime('%H:%M:%S')}]", *a, file=sys.stderr, flush=True)


def coset_action_reps(V, mats):
    """pbar.coset_action, also returning the BFS representatives mod 3."""
    pmV = np.array([u % 3 for u in V] + [(-u) % 3 for u in V],
                   dtype=np.int64)
    m3 = [A % 3 for A in mats]

    def canon(X):
        prods = np.einsum("uij,jk->uik", pmV, X) % 3
        return int(S.key3(prods).min())

    start = np.eye(4, dtype=np.int64)
    index, reps, act = {canon(start): 0}, [start], []
    q = 0
    while q < len(reps):
        X = reps[q]
        row = []
        for B in m3:
            Y = (X @ B) % 3
            k = canon(Y)
            if k not in index:
                index[k] = len(reps)
                reps.append(Y)
            row.append(index[k])
        act.append(row)
        q += 1
    return act, reps


def inv3(X):
    """Inverse of a symplectic matrix mod 3."""
    return pbar.sinv(X) % 3


def order3_subgroups(Phi):
    I = np.eye(4, dtype=np.int64)
    subs, found = [], set()
    for A in Phi:
        if S.key3(A) == S.key3(I):
            continue
        Sg = S.subgroup_closure([A])
        fk = frozenset(S.key3(X) for X in Sg)
        if len(Sg) == 3 and fk not in found:
            found.add(fk)
            subs.append(Sg)
    subs.sort(key=lambda M: sorted(S.key3(X) for X in M))
    return subs


def quotient_map(Phi, L):
    """key3 of each element of +-B -> its class in B/L = Z/3 (B = Phi, or
    U for the test runs; L normal of index 3 in B)."""
    lk = {S.key3(X) for X in L}
    a = next(X for X in Phi if S.key3(X) not in lk)
    powers = [np.eye(4, dtype=np.int64), a % 3, (a @ a) % 3]
    phi = {}
    for g in Phi:
        for i, ai in enumerate(powers):
            if S.key3((g @ inv3(ai)) % 3) in lk:
                phi[S.key3(g)] = i
                phi[S.key3((-g) % 3)] = i
                break
    assert len(phi) == 2 * len(Phi)
    return phi


def build(which, trivial=False, base="phi"):
    """which: index of the order-3 subgroup L of Phi (sorted by key3), or
    'z' for the centre Z(U); with base='U', which = 'max<k>' (the maximal
    subgroups of U, a test against the census of pbar.py).  Returns (ngen, rels, twists, info) with R-rows
    as dicts gen -> [a0, a1, a2] (coefficient of t^0, t^1, t^2)."""
    t0 = time.time()
    rels = P.check_presentation()
    table = P.conj_table()
    tw = P.standard_twists(table)
    twists = [tuple(w) + tuple(w) for _, w in sorted(tw.items())]
    mats = pbar.pure_mats()
    relators = [tuple(u) + P.finv(tuple(v)) for u, v in rels]
    relators.append(tuple(P.delta2_pure()))
    Phi = S.subgroup("phi")
    subs = order3_subgroups(Phi)
    U = S.sylow_U(S.sp4_f3())
    Zc = [A for A in U
          if all(S.key3((A @ B) % 3) == S.key3((B @ A) % 3) for B in U)]
    zk = frozenset(S.key3(X) for X in Zc)
    zidx = [i for i, M in enumerate(subs)
            if frozenset(S.key3(X) for X in M) == zk]
    assert len(subs) == 4 and len(zidx) == 1
    if base == "U":
        B, L = U, S.subgroup(which)
    else:
        if which == "z":
            which = zidx[0]
        B, L = Phi, subs[int(which)]
    phi = quotient_map(B, L)
    act, reps = coset_action_reps(B, mats)
    inv = pbar.inverse_action(act)
    gen = pbar.schreier(act)
    ng = len(act[0])
    m3 = [A % 3 for A in mats]
    rinv = [inv3(X) for X in reps]
    volt = [[0] * ng for _ in act]
    for c in range(len(act)):
        for p in range(ng):
            d = act[c][p]
            g = (reps[c] @ m3[p] @ rinv[d]) % 3
            k = S.key3(g)
            assert k in phi, "Schreier generator outside +-B"
            v = 0 if trivial else phi[k]
            if (c, p) not in gen:
                assert v == 0 and (g == np.eye(4, dtype=np.int64)).all()
            volt[c][p] = v
    log(f"L = subgroup {which} (Z(U) is {zidx[0]}), {len(act)} base cosets, "
        f"{len(gen)} Schreier gens [{time.time()-t0:.0f}s]")

    def trace(c, word):
        vec, s = {}, 0
        for a in word:
            if a > 0:
                p = a - 1
                g = gen.get((c, p))
                if g is not None:
                    e = vec.setdefault(g, [0, 0, 0])
                    e[s] += 1
                s = (s + volt[c][p]) % 3
                c = act[c][p]
            else:
                p = -a - 1
                c = inv[c][p]
                s = (s - volt[c][p]) % 3
                g = gen.get((c, p))
                if g is not None:
                    e = vec.setdefault(g, [0, 0, 0])
                    e[s] -= 1
        return c, s, {g: e for g, e in vec.items() if any(e)}

    R = []
    for w in relators:
        for c in range(len(act)):
            e, s, vec = trace(c, w)
            assert e == c and s == 0
            if vec:
                R.append(vec)
    Z, zinfo = [], []
    for c in range(len(act)):
        for k, w in enumerate(twists):
            e, s, vec = trace(c, w)
            assert e == c and s == 0
            Z.append(vec)
            zinfo.append((c, k))
    info = {"base": base, "L": str(which), "Z_index": zidx[0],
            "base_cosets": len(act), "schreier_gens": len(gen),
            "relator_rows": len(R), "twist_rows": len(Z)}
    log(f"built {len(R)} relator rows, {len(Z)} twist rows "
        f"[{time.time()-t0:.0f}s]")
    return len(gen), R, Z, zinfo, info
