#!/usr/bin/env python3
"""Same census as sylow.py, in the pure model Pbar = P_5/<Delta^2> = PMod(S_{0,6}).

Pbar is the image of pi^-1 Gamma(2) in Mod(S_{0,6}); its image in Sp_4(Z)/+-I
is Gamma(2)/+-I.  For V <= U (the 3-Sylow of sylow.py), M_V is the
stabilizer in Pbar of the coset (+-V) X of Sp_4(F_3), so Pbar/M_V has
25920/|V| cosets (320 for V = U, 25920 for V = 1, i.e. Gamma(6)).

Separating twists: a separating curve of S_2 covers a round curve about a
3-subset A of {1..5} (puncture 6 outside), and t_s maps to T_A^2 with
T_A = (s1 s2)^3 conjugated (pure.py standard_twists).  The census classes
are the H_1(M_V)-classes of g_c T_A^2 g_c^-1 over cosets c and the 10 triples.
The presentation, Delta^2 word and twist words are the machine-checked ones
of ../mod-s2-palindrome-transversal-relations-2026-09-17/pure.py.

Usage: python3 pbar.py <U|max0..max3|phi|one> [out.json]
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-palindrome-transversal-relations-2026-09-17"))
import pure as P  # noqa: E402
import sylow as S  # noqa: E402

C = S.C
J = C.J


def sinv(A):
    return -J @ A.T @ J


def sigma_mat(a):
    A = C.GENMATS[abs(a) - 1]
    return A if a > 0 else sinv(A)


def pure_mats():
    mats = []
    for p in range(len(P.PAIRS)):
        X = np.eye(4, dtype=np.int64)
        for a in P.pure_to_sigma((p + 1,)):
            X = X @ sigma_mat(a)
        mats.append(X)
    return mats


def word_mat(word, mats):
    X = np.eye(4, dtype=np.int64)
    for a in word:
        X = X @ (mats[a - 1] if a > 0 else sinv(mats[-a - 1]))
    return X


def is_pm_identity(X):
    I = np.eye(4, dtype=np.int64)
    return (X == I).all() or (X == -I).all()


def coset_action(V, mats):
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
    return act


def inverse_action(act):
    inv = [[None] * len(act[0]) for _ in act]
    for c, row in enumerate(act):
        for p, d in enumerate(row):
            inv[d][p] = c
    return inv


def schreier(act):
    k, ng = len(act), len(act[0])
    seen = [False] * k
    seen[0] = True
    tree, queue = set(), [0]
    for c in queue:
        for p in range(ng):
            d = act[c][p]
            if not seen[d]:
                seen[d] = True
                tree.add((c, p))
                queue.append(d)
    assert all(seen)
    gen = {}
    for c in range(k):
        for p in range(ng):
            if (c, p) not in tree:
                gen[(c, p)] = len(gen)
    return gen


def trace(act, inv, gen, c, word, vec, sgn=1):
    for a in word:
        if a > 0:
            g = gen.get((c, a - 1))
            if g is not None:
                vec[g] = vec.get(g, 0) + sgn
            c = act[c][a - 1]
        else:
            c = inv[c][-a - 1]
            g = gen.get((c, -a - 1))
            if g is not None:
                vec[g] = vec.get(g, 0) - sgn
    return c


def centralizer_words(tw_words):
    """For each twist word w, the pure words h among A_ij^(+-1), T_A (all
    triples) that commute with w in P_5 (checked in Aut(F_5))."""
    cands = [(p + 1,) for p in range(len(P.PAIRS))]
    table = P.conj_table()
    cands += [tuple(w) for _, w in sorted(P.standard_twists(table).items())]
    out = []
    for w in tw_words:
        aw = P.aut_pure(w)
        hs = []
        for h in cands:
            ah = P.aut_pure(h)
            if P.compose(ah, aw) == P.compose(aw, ah):
                hs.append(h)
        out.append(hs)
    return out


def orbit_reps(act, inv, words):
    """Orbits of the cosets under the right action of the given pure words.
    If h commutes with the twist w, the H_1(M_V)-class of g_c w g_c^-1 is
    constant on these orbits (g_{c.h} = m g_c h with m in M_V)."""
    k = len(act)
    rep = [None] * k
    reps, size = [], []
    for c0 in range(k):
        if rep[c0] is not None:
            continue
        rep[c0] = c0
        stack, n = [c0], 1
        while stack:
            c = stack.pop()
            for h in words:
                d = trace(act, inv, {}, c, h, {})
                if rep[d] is None:
                    rep[d] = c0
                    stack.append(d)
                    n += 1
        reps.append(c0)
        size.append(n)
    return reps, size


def rs(act, relators, twists, reduce_twists=False):
    inv = inverse_action(act)
    gen = schreier(act)
    if reduce_twists:
        cw = centralizer_words(twists)
        vs, mult = [], []
        for w, hs in zip(twists, cw):
            reps, size = orbit_reps(act, inv, hs)
            for c, n in zip(reps, size):
                vec = {}
                assert trace(act, inv, gen, c, w, vec) == c
                vs.append({g: a for g, a in vec.items() if a})
                mult.append(n)
        rs.last_twist_info = {"centralizer_sizes": [len(h) for h in cw],
                              "twist_vectors": len(vs)}
        rs.last_mult = mult
    rels = []
    for u, v in relators:
        for c in range(len(act)):
            vec = {}
            e1 = trace(act, inv, gen, c, u, vec, 1)
            e2 = trace(act, inv, gen, c, v, vec, -1)
            assert e1 == e2
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rels.append(vec)
    if reduce_twists:
        return len(gen), rels, vs
    vs = []
    for c in range(len(act)):
        for w in twists:
            vec = {}
            assert trace(act, inv, gen, c, w, vec) == c
            vs.append({g: a for g, a in vec.items() if a})
    return len(gen), rels, vs


def main(name, outp, fast=False):
    t0 = time.time()
    rels = P.check_presentation()
    table = P.conj_table()
    tw = P.standard_twists(table)
    twists = [tuple(w) + tuple(w) for _, w in sorted(tw.items())]
    mats = pure_mats()
    for u, v in rels:
        assert is_pm_identity(word_mat(u, mats) @ sinv(word_mat(v, mats)))
    assert is_pm_identity(word_mat(P.delta2_pure(), mats))
    for w in twists:
        assert (word_mat(w, mats) == np.eye(4, dtype=np.int64)).all()
    relators = list(rels) + [(P.delta2_pure(), ())]
    V = S.subgroup(name)
    act = coset_action(V, mats)
    print(f"[{name}] |V| = {len(V)}, Pbar cosets {len(act)} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    ngen, R, vs = rs(act, relators, twists, reduce_twists=fast)
    print(f"[{name}] Schreier gens {ngen}, relators {len(R)}, twist "
          f"vectors {len(vs)} [{time.time()-t0:.0f}s]", flush=True)
    elim = None
    if fast:
        import fastelim
        elim = fastelim.eliminate
        print(f"[{name}] twist reduction {rs.last_twist_info}", flush=True)
    out, (cols, H, keys, cls_of, B) = S.lattice_from_rs(
        ngen, R, vs, f"pbar-{name}", len(act), elim=elim)
    if fast:
        cnt = [0] * len(keys)
        for c, n in zip(cls_of, rs.last_mult):
            cnt[c] += n
        assert sum(cnt) == 10 * len(act)
        out["class_coset_counts"] = sorted(set(cnt))
        out["mode"] = "fast (Markowitz pivots, centralizer-orbit twist reps)"
    out["V_order"] = len(V)
    json.dump(out, open(outp, "w"), indent=1)
    print("saved", outp, flush=True)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a != "--fast"]
    fast = "--fast" in sys.argv[1:]
    nm = args[0]
    sfx = "-fast" if fast else ""
    main(nm, args[1] if len(args) > 1 else
         os.path.join(HERE, f"pbar-{nm}{sfx}.json"), fast=fast)
