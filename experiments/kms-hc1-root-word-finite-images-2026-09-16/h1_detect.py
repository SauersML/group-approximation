#!/usr/bin/env python3
"""Scan 4 (2026-09-16): exact integral detection of w_p in H_1 of point stabilisers.

For a finite permutation image of Gamma_p (generators a,b,c acting on an orbit
Omega containing a base point w0, with w_p acting trivially), let H be the
stabiliser of w0.  The covering 2-complex of the presentation complex with
vertex set Omega gives
    Z^{E} / im(d_2)  =  H_1(H;Z)  (+)  Z^{|Omega|-1},    E = 3|Omega| edges,
and the 1-chain c_w of the closed walk reading w_p from w0 is a cycle, so
    [w_p] = 0 in H_1(H;Z)   <=>   c_w lies in the Z-row-span of d_2.
This is an exact integer computation (no reduction mod l), so it detects
[w_p] of any order, including l^k-torsion invisible mod l.
Method: sparse elimination on +-1 pivots (unimodular, keeps the quotient and
tracks c_w), then dense Hermite-style elimination over Z on the remainder,
then exact reduction of c_w.  Also prints the torsion invariants of the
remainder (the torsion part of H_1(H;Z)).
Usage: h1_detect.py sl3 <p> {points|lines|vectors}
       h1_detect.py sl4 <p> {R1|R2} {points|hyperplanes}
"""
import itertools
import sys

import numpy as np

import kmslib as K


def orbit_perms(mats, p, kind, n):
    vecs = [v for v in itertools.product(range(p), repeat=n) if any(v)]
    if kind == "vectors":
        pts = vecs
        norm = lambda v: v
    else:
        pts = sorted({K.normalize(v, p) for v in vecs})
        norm = lambda v: K.normalize(v, p)
    index = {pt: i for i, pt in enumerate(pts)}
    perms = []
    for g in mats:
        g = np.array(g, dtype=np.int64) % p
        gi = K.mat_inv_mod(g, p)
        # right action  w.x := rho(x)^{-1} w  (points) ; hyperplanes phi.x := phi rho(x)
        img = []
        for pt in pts:
            if kind in ("points", "vectors"):
                q = tuple(int(x) % p for x in gi @ np.array(pt))
            else:
                q = tuple(int(x) % p for x in np.array(pt) @ g)
            img.append(index[norm(q)])
        perms.append(img)
    return pts, perms


def inverse_perm(pm):
    inv = [0] * len(pm)
    for i, j in enumerate(pm):
        inv[j] = i
    return inv


def walk_chain(word, start, perms, invs):
    """Chain on edges (x, w) [edge w -> w.x] of the walk reading word from start."""
    ch = {}
    w = start
    for (g, e) in word:
        if e == 1:
            key = (g, w)
            ch[key] = ch.get(key, 0) + 1
            w = perms[g][w]
        else:
            w2 = invs[g][w]
            key = (g, w2)
            ch[key] = ch.get(key, 0) - 1
            w = w2
    return {k: v for k, v in ch.items() if v}, w


def orbit_of(start, perms):
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for pm in perms:
            y = pm[x]
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return sorted(seen)


def analyse(label, perms, p, start=0, word=None, wname="w_p"):
    invs = [inverse_perm(pm) for pm in perms]
    orb = orbit_of(start, perms)
    orbset = set(orb)
    rels = []
    for (_, u) in K.relators(p):
        for w0 in orb:
            ch, end = walk_chain(u, w0, perms, invs)
            assert end == w0, "relator not closed"
            if ch:
                rels.append(ch)
    word = K.root_word(p) if word is None else word
    cw, end = walk_chain(word, start, perms, invs)
    if end != start:
        print(f"{label}: {wname} moves the base point")
        return
    # sparse elimination on +-1 pivots
    col_rows = {}
    for i, r in enumerate(rels):
        for k in r:
            col_rows.setdefault(k, set()).add(i)
    alive = set(range(len(rels)))
    ncols0 = 3 * len(orb)
    progress = True
    while progress:
        progress = False
        for i in list(alive):
            if i not in alive:
                continue
            r = rels[i]
            piv = next((k for k, v in r.items() if v in (1, -1)), None)
            if piv is None:
                continue
            sgn = r[piv]
            # eliminate piv from every other row and from c_w
            for j in list(col_rows.get(piv, ())):
                if j == i or j not in alive:
                    continue
                rj = rels[j]
                f = rj.get(piv, 0) * sgn
                if f:
                    for k, v in r.items():
                        nv = rj.get(k, 0) - f * v
                        if nv:
                            rj[k] = nv
                            col_rows.setdefault(k, set()).add(j)
                        elif k in rj:
                            del rj[k]
                            col_rows[k].discard(j)
            f = cw.get(piv, 0) * sgn
            if f:
                for k, v in r.items():
                    nv = cw.get(k, 0) - f * v
                    if nv:
                        cw[k] = nv
                    elif k in cw:
                        del cw[k]
            for k in r:
                col_rows[k].discard(i)
            alive.discard(i)
            del col_rows[piv]
            progress = True
            for j in list(alive):
                if not rels[j]:
                    alive.discard(j)
    cols = sorted({k for i in alive for k in rels[i]} | set(cw))
    idx = {k: t for t, k in enumerate(cols)}
    M = [[0] * len(cols) for _ in alive]
    for t, i in enumerate(sorted(alive)):
        for k, v in rels[i].items():
            M[t][idx[k]] = v
    target = [0] * len(cols)
    for k, v in cw.items():
        target[idx[k]] = v
    remaining_cols = ncols0 - (ncols0 - len(col_rows))  # columns still present
    # dense integral echelon form (row HNF-like) with target reduction
    rows = [r[:] for r in M]
    piv_rows = []
    col = 0
    diag = []
    for col in range(len(cols)):
        cand = [r for r in rows if r[col] != 0]
        if not cand:
            continue
        rest = [r for r in rows if r[col] == 0]
        while len(cand) > 1:
            cand.sort(key=lambda r: abs(r[col]))
            pr = cand[0]
            new = [pr]
            for r in cand[1:]:
                q = r[col] // pr[col]
                r2 = [x - q * y for x, y in zip(r, pr)]
                if r2[col] != 0:
                    new.append(r2)
                elif any(r2):
                    rest.append(r2)
            cand = new
        pr = cand[0]
        if pr[col] < 0:
            pr = [-x for x in pr]
        piv_rows.append((col, pr))
        diag.append(pr[col])
        rows = rest
    t = target[:]
    for (col, pr) in piv_rows:
        if t[col] % pr[col]:
            break
        q = t[col] // pr[col]
        t = [x - q * y for x, y in zip(t, pr)]
    zero = not any(t)
    present_cols = len(col_rows)
    free_rank = present_cols - len(piv_rows)
    tors = [d for d in diag if d != 1]
    print(f"{label}: |orbit|={len(orb)} rows={len(rels)} after_sparse rows={len(alive)} "
          f"cols={len(cols)} free_rank(Z^E/im d2)={free_rank} (expect |orbit|-1={len(orb)-1}) "
          f"echelon pivots!=1 (not SNF)={tors} "
          f"[{wname}]=0 in H_1(H;Z): {zero}", flush=True)


if __name__ == "__main__":
    fam = sys.argv[1]
    p = int(sys.argv[2])
    E = lambda n, terms: K_elem(n, p, terms)

    def K_elem(n, p, terms):
        M = np.eye(n, dtype=np.int64)
        for (i, j, e) in terms:
            M[i, j] = (M[i, j] + e) % p
        return M

    if fam == "sl3":
        kind = sys.argv[3]
        mats = [K_elem(3, p, [(0, 1, 1)]), K_elem(3, p, [(1, 2, 1)]), K_elem(3, p, [(2, 0, 1)])]
        pts, perms = orbit_perms(mats, p, kind, 3)
        analyse(f"SL3 p={p} {kind}", perms, p)
        if len(sys.argv) > 4 and sys.argv[4] == "control":
            a, b, c = K.gen(0), K.gen(1), K.gen(2)
            for nm, u in [("a", a), ("b", b), ("c", c), ("[a,b]", K.comm(a, b)),
                          ("[b,c]", K.comm(b, c)), ("[a,c]", K.comm(a, c)), ("a^p", a * p)]:
                analyse(f"  control p={p} {kind}", perms, p, word=u, wname=nm)
    else:
        name, kind = sys.argv[3], sys.argv[4]
        reps = {"R1": [[(0, 1, 1)], [(2, 0, 1)], [(1, 2, 1), (2, 3, 1)]],
                "R2": [[(0, 1, 1)], [(1, 2, 1)], [(1, 2, 1), (2, 3, 1)]]}
        mats = [K_elem(4, p, t) for t in reps[name]]
        pts, perms = orbit_perms(mats, p, kind, 4)
        seen = set()
        for s in range(len(pts)):
            if s in seen:
                continue
            orb = orbit_of(s, perms)
            seen |= set(orb)
            analyse(f"SL4 {name} p={p} {kind} orbit-rep={pts[s]}", perms, p, start=s)
