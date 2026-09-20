#!/usr/bin/env python3
"""Two-stage Reidemeister-Schreier for the 3-Sylow chain, with Tietze
elimination in between.

Stage 1. Reidemeister-Schreier for M_U inside Pbar = P_5/<Delta^2> (320
cosets, pbar.py), keeping the relators as WORDS in the Schreier generators,
followed by Tietze elimination (a generator occurring exactly once in a
relator is solved for and substituted everywhere).  The result is a small
presentation of M_U, each surviving generator carrying its image in U
(an element of Sp_4(F_3), the sign fixed by -I not in U).  The separating
twists g_r T_A^2 g_r^-1 (r a coset of M_U, A a triple) are carried along as
words in the same generators.

Stage 2. For V' <= U, M_V' is the preimage of V' under M_U -> U, of index
[U : V'].  Abelian Reidemeister-Schreier over the cosets V' u of U gives
H_1(M_V') and the classes of all separating twists of M_V': every twist of
M_V' is g t g^-1 with g = m g_r, m in M_U, and its class is the trace of the
word x_{r,A} = g_r T_A^2 g_r^-1 from the coset V' img(m).

Every Tietze move is an exact group isomorphism, so stage 2 computes the
same groups as pbar.py; `python3 tietze_chain.py U` and `max0`
reproduce pbar-U.json and pbar-max0.json (checked in the log).

With --fast only centralizer-orbit representatives of the twists are
formed (as in `pbar.py --fast`): a twist g T_A^2 g^-1 of M_V' with g of
mod-3 image X is rewritten as m x_{r,A} m^-1, r the level-one coset of X
and m in M_U of image u = X X_r^-1 in U, so its class is the trace of
x_{r,A} from the coset V' u.  Orbit sizes weight class_coset_counts.

With --via W (repeatable, --fast only) the passage U > W > V' is done in
two steps: a non-abelian Reidemeister-Schreier to M_W (refine), a second
Tietze pass, and only then the abelian stage 2.

Usage: python3 tietze_chain.py <U|max0..max3|phi|z|phisub<k>|one>
       [--fast] [--via W ...]
"""
import heapq
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pbar as PB  # noqa: E402
import sylow as S  # noqa: E402
import fastelim  # noqa: E402

P = PB.P
C = S.C


def log(*a):
    print(*a, flush=True)


# ------------------------------------------------------------ stage 1 data
def level_one(U, mats):
    """Cosets (+-U) X of Sp_4(F_3) under the pure generators, with reps."""
    pmU = np.array([u % 3 for u in U] + [(-u) % 3 for u in U],
                   dtype=np.int64)
    m3 = [A % 3 for A in mats]

    def canon(X):
        return int(S.key3(np.einsum("uij,jk->uik", pmU, X) % 3).min())

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


def f3_inv(X):
    return (-S.J3 @ X.T @ S.J3) % 3


def word_trace(act, inv, gen, c, word):
    """Word in Schreier generators (letters +-(id+1)) for the loop."""
    out = []
    for a in word:
        if a > 0:
            g = gen.get((c, a - 1))
            if g is not None:
                out.append(g + 1)
            c = act[c][a - 1]
        else:
            c = inv[c][-a - 1]
            g = gen.get((c, -a - 1))
            if g is not None:
                out.append(-(g + 1))
    return c, out


def freduce(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out


def creduce(w):
    w = freduce(w)
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1
        j -= 1
    return w[i:j + 1]


def winv(w):
    return [-a for a in reversed(w)]


# ------------------------------------------------------------ Tietze
def tietze(ngen, rels, words, max_len=4000, log_every=200, grow=1.6):
    """Eliminate generators occurring exactly once in some relator.
    rels: list of cyclically reduced words; words: carried words (twists).
    Stops once the total relator length exceeds `grow` times its minimum
    (word growth then outweighs the saving in generators).
    Returns (alive generator ids, relators, words)."""
    t0 = time.time()
    rels = {i: creduce(r) for i, r in enumerate(rels)}
    rels = {i: r for i, r in rels.items() if r}
    total = sum(len(r) for r in rels.values())
    tmin = total
    words = [freduce(w) for w in words]
    occ = {}                      # gen -> set of relator ids
    for i, r in rels.items():
        for a in r:
            occ.setdefault(abs(a), set()).add(i)
    wocc = {}
    for i, w in enumerate(words):
        for a in w:
            wocc.setdefault(abs(a), set()).add(i)
    alive = set(range(1, ngen + 1))
    heap = []

    def push(i):
        r = rels[i]
        cnt = {}
        for a in r:
            cnt[abs(a)] = cnt.get(abs(a), 0) + 1
        best = None
        for g, n in cnt.items():
            if n == 1:
                c = sum(1 for _ in occ.get(g, ()))
                if best is None or c < best[0]:
                    best = (c, g)
        if best is not None:
            heapq.heappush(heap, ((len(r) - 1) * max(best[0] - 1, 0),
                                  len(r), i, best[1]))

    for i in rels:
        push(i)
    steps = 0
    while heap:
        cost, L, i, g = heapq.heappop(heap)
        r = rels.get(i)
        if r is None:
            continue
        if len(r) != L or sum(1 for a in r if abs(a) == g) != 1:
            push(i)
            continue
        true = (len(r) - 1) * max(len(occ.get(g, ())) - 1, 0)
        if true > cost:
            heapq.heappush(heap, (true, L, i, g))
            continue
        if len(r) - 1 > max_len:
            continue
        # r = u g^e v  =>  g^e = u^-1 v^-1 ... rotate: g^e w = 1
        k = next(t for t, a in enumerate(r) if abs(a) == g)
        e = 1 if r[k] > 0 else -1
        w = r[k + 1:] + r[:k]
        val = winv(w) if e == 1 else w          # value of g
        vinv = winv(val)
        if total > grow * tmin:
            break
        del rels[i]
        total -= len(r)
        for a in r:
            occ.get(abs(a), set()).discard(i)

        def subst(word):
            out = []
            for a in word:
                if a == g:
                    out.extend(val)
                elif a == -g:
                    out.extend(vinv)
                else:
                    out.append(a)
            return out

        for j in list(occ.get(g, ())):
            old = rels[j]
            new = creduce(subst(old))
            for a in old:
                occ.get(abs(a), set()).discard(j)
            total += len(new) - len(old)
            if new:
                rels[j] = new
                for a in new:
                    occ.setdefault(abs(a), set()).add(j)
                push(j)
            else:
                del rels[j]
        for j in list(wocc.get(g, ())):
            old = words[j]
            new = freduce(subst(old))
            for a in old:
                wocc.get(abs(a), set()).discard(j)
            words[j] = new
            for a in new:
                wocc.setdefault(abs(a), set()).add(j)
        occ.pop(g, None)
        wocc.pop(g, None)
        alive.discard(g)
        steps += 1
        if steps % log_every == 0:
            tot = sum(len(x) for x in rels.values())
            log(f"  tietze: {steps} eliminated, {len(alive)} gens, "
                f"{len(rels)} rels, total length {tot}, max twist word "
                f"{max(len(x) for x in words)} [{time.time()-t0:.0f}s]")
    return sorted(alive), list(rels.values()), words


# ------------------------------------------------------------ twist reps
def pbar_cosets(V, mats):
    """PB.coset_action for M_V in Pbar, also returning the exact mod-3
    images of the BFS tree words (the Schreier transversal g_c)."""
    pmV = np.array([u % 3 for u in V] + [(-u) % 3 for u in V],
                   dtype=np.int64)
    m3 = [A % 3 for A in mats]

    def canon(X):
        return int(S.key3(np.einsum("uij,jk->uik", pmV, X) % 3).min())

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


def twist_reps(V, mats, twists, U, lvl_act, lvl_reps):
    """Centralizer-orbit representatives of the separating twists of M_V
    (as in pbar.rs with reduce_twists=True), each rewritten as
    m x_{r,A} m^-1 with m in M_U: returns [(r, A, u, mult)], u = image of
    m in U.  g_c = m g_r, so u = X_c X_r^-1, sign fixed by -I not in U."""
    act, reps = pbar_cosets(V, mats)
    inv = PB.inverse_action(act)
    cw = PB.centralizer_words(twists)
    ukeys = {S.key3(u % 3) for u in U}
    pmU = np.array([u % 3 for u in U] + [(-u) % 3 for u in U],
                   dtype=np.int64)
    lvl_index = {}
    for r, X in enumerate(lvl_reps):
        lvl_index[int(S.key3(np.einsum("uij,jk->uik", pmU, X) % 3).min())] = r
    out = []
    for A, hs in enumerate(cw):
        creps, size = PB.orbit_reps(act, inv, hs)
        for c, n in zip(creps, size):
            X = reps[c]
            r = lvl_index[int(S.key3(np.einsum("uij,jk->uik", pmU, X)
                                     % 3).min())]
            u = (X @ f3_inv(lvl_reps[r])) % 3
            if S.key3(u) not in ukeys:
                u = (-u) % 3
            assert S.key3(u) in ukeys
            out.append((r, A, u, n))
    assert sum(t[3] for t in out) == 10 * len(act)
    return out, len(act), [len(h) for h in cw]


# ------------------------------------------------------------ refinement
def refine(gens, img, rels, twords, Vsub, label):
    """Non-abelian Reidemeister-Schreier from the presented group G (gens,
    images in U, relator words, carried twist words) to the preimage G' of
    Vsub.  Returns the presentation of G' in the same format, the carried
    words x traced from every coset (list index = old index * k + coset),
    and (index, reps, canon) to locate cosets: a twist m x m^-1 with m in G
    of image u is m' x' m'^-1 with x' = the trace from the coset c of u and
    m' in G' of image u X_c^-1."""
    t0 = time.time()
    Vk = [v % 3 for v in Vsub]

    def canon(X):
        return int(min(S.key3((v @ X) % 3) for v in Vk))

    I = np.eye(4, dtype=np.int64)
    index, reps, act = {canon(I): 0}, [I], []
    q = 0
    while q < len(reps):
        X = reps[q]
        row = []
        for g in gens:
            Y = (X @ img[g]) % 3
            k = canon(Y)
            if k not in index:
                index[k] = len(reps)
                reps.append(Y)
            row.append(index[k])
        act.append(row)
        q += 1
    k = len(act)
    inv = PB.inverse_action(act)
    sg = PB.schreier(act)
    pos = {g: t for t, g in enumerate(gens)}
    loc = lambda w: [(pos[abs(a)] + 1) * (1 if a > 0 else -1) for a in w]
    vk = {S.key3(v) for v in Vk}
    nimg = {}
    for (c, p), gid in sg.items():
        d = act[c][p]
        Y = (reps[c] @ img[gens[p]] @ f3_inv(reps[d])) % 3
        assert S.key3(Y) in vk
        nimg[gid + 1] = Y
    nrels = []
    for r in rels:
        lr = loc(r)
        for c in range(k):
            e, w = word_trace(act, inv, sg, c, lr)
            assert e == c
            nrels.append(w)
    ntw = []
    for w in twords:
        lw = loc(w)
        for c in range(k):
            e, x = word_trace(act, inv, sg, c, lw)
            assert e == c
            ntw.append(x)
    log(f"[{label}] refine: {k} cosets, {len(sg)} gens, {len(nrels)} "
        f"relators, {len(ntw)} carried words [{time.time()-t0:.0f}s]")
    return (list(range(1, len(sg) + 1)), nimg, nrels, ntw,
            (index, reps, canon, k))


# ------------------------------------------------------------ stage 2
def stage_two(Uel, Vsub, gens, img, rels, twords, label, treps=None):
    """Abelian RS for M_V' in the Tietze presentation of M_U.
    treps: optional [(r, A, u, mult)] from twist_reps; then only those
    twist vectors are formed (x_{r,A} traced from the coset V' u)."""
    ukey = {S.key3(u): i for i, u in enumerate(Uel)}
    Vk = [v % 3 for v in Vsub]

    def canon(X):
        return int(min(S.key3((v @ X) % 3) for v in Vk))

    pos = {g: t for t, g in enumerate(gens)}
    I = np.eye(4, dtype=np.int64)
    index, reps, act = {canon(I): 0}, [I], []
    q = 0
    while q < len(reps):
        X = reps[q]
        row = []
        for g in gens:
            Y = (X @ img[g]) % 3
            k = canon(Y)
            if k not in index:
                index[k] = len(reps)
                reps.append(Y)
            row.append(index[k])
        act.append(row)
        q += 1
    assert len(act) == len(Uel) // len(Vsub)
    inv = PB.inverse_action(act)
    sg = PB.schreier(act)
    # letters in local numbering
    loc = lambda w: [(pos[abs(a)] + 1) * (1 if a > 0 else -1) for a in w]
    R = []
    for r in rels:
        lw = loc(r)
        for c in range(len(act)):
            vec = {}
            assert PB.trace(act, inv, sg, c, lw, vec) == c
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                R.append(vec)
    vs = []
    if treps is None:
        for w in twords:
            lw = loc(w)
            for c in range(len(act)):
                vec = {}
                assert PB.trace(act, inv, sg, c, lw, vec) == c
                vs.append({g: a for g, a in vec.items() if a})
    else:
        for idx, u, _ in treps:
            c = index[canon(u)]
            lw = loc(twords[idx])
            vec = {}
            assert PB.trace(act, inv, sg, c, lw, vec) == c
            vs.append({g: a for g, a in vec.items() if a})
    log(f"[{label}] stage 2: {len(act)} cosets of M_V' in the top group, "
        f"{len(sg)} Schreier gens, {len(R)} relator rows, "
        f"{len(vs)} twist vectors")
    ncos = 25920 // len(Vsub)
    return S.lattice_from_rs(len(sg), R, vs, label, ncos,
                             elim=fastelim.eliminate)


def main(name, fast=False, via=()):
    t0 = time.time()
    rels = P.check_presentation()
    table = P.conj_table()
    tw = P.standard_twists(table)
    twists = [tuple(w) + tuple(w) for _, w in sorted(tw.items())]
    mats = PB.pure_mats()
    relators = list(rels) + [(P.delta2_pure(), ())]
    allg = S.sp4_f3()
    U = S.sylow_U(allg)
    ukeys = {S.key3(u % 3) for u in U}
    act, reps = level_one(U, mats)
    assert len(act) == 320
    inv = PB.inverse_action(act)
    gen = PB.schreier(act)
    # images in U of the Schreier generators (c, p) = X_c B_p X_d^-1
    img = {}
    for (c, p), gid in gen.items():
        d = act[c][p]
        Y = (reps[c] @ (mats[p] % 3) @ f3_inv(reps[d])) % 3
        if S.key3(Y) not in ukeys:
            Y = (-Y) % 3
        assert S.key3(Y) in ukeys
        img[gid + 1] = Y
    words = []
    for u, v in relators:
        for c in range(len(act)):
            e1, w1 = word_trace(act, inv, gen, c, u)
            e2, w2 = word_trace(act, inv, gen, c, v)
            assert e1 == e2
            words.append(w1 + winv(w2))
    twords = []
    for c in range(len(act)):
        for w in twists:
            e, x = word_trace(act, inv, gen, c, w)
            assert e == c
            twords.append(x)
    log(f"[{name}] stage 1: {len(gen)} Schreier gens of M_U, {len(words)} "
        f"relators, {len(twords)} twist words [{time.time()-t0:.0f}s]")

    def image(w):
        X = np.eye(4, dtype=np.int64)
        for a in w:
            X = (X @ (img[a] if a > 0 else f3_inv(img[-a]))) % 3
        return X

    I = np.eye(4, dtype=np.int64)
    for w in words[::97]:
        assert (image(w) == I).all()
    alive, trels, ttw = tietze(len(gen), words, twords)
    tot = sum(len(r) for r in trels)
    log(f"[{name}] Tietze: {len(alive)} gens, {len(trels)} relators, total "
        f"length {tot}, twist word lengths up to "
        f"{max(len(w) for w in ttw)} [{time.time()-t0:.0f}s]")
    for w in trels[::max(1, len(trels) // 200)]:
        assert (image(w) == I).all()
    for w in ttw[::max(1, len(ttw) // 200)]:
        assert (image(w) == I).all()
    Vsub = S.subgroup(name)
    treps = None
    sfx = ""
    if fast:
        tr, npb, csz = twist_reps(Vsub, mats, twists, U, act, reps)
        treps = [(r * 10 + A, u, n) for r, A, u, n in tr]
        log(f"[{name}] {npb} Pbar cosets, centralizer sizes {csz}, "
            f"{len(treps)} twist representatives [{time.time()-t0:.0f}s]")
        sfx = "-fast"
    top = U
    for wname in via:
        assert fast
        Wsub = S.subgroup(wname)
        alive, img, nrels, ttw, (index, wreps, canon, k) = refine(
            alive, img, trels, ttw, Wsub, f"{name} via {wname}")
        new = []
        for idx, u, n in treps:
            c = index[canon(u)]
            new.append((idx * k + c, (u @ f3_inv(wreps[c])) % 3, n))
        treps = new
        # keep only the carried words that are still needed
        need = sorted({t[0] for t in treps})
        renum = {o: i for i, o in enumerate(need)}
        ttw = [ttw[o] for o in need]
        treps = [(renum[i], u, n) for i, u, n in treps]
        alive, trels, ttw = tietze(len(alive), nrels, ttw)
        log(f"[{name} via {wname}] Tietze: {len(alive)} gens, {len(trels)} "
            f"relators, total length {sum(len(r) for r in trels)} "
            f"[{time.time()-t0:.0f}s]")
        img = {g: img[g] for g in alive}
        top = Wsub
        sfx = sfx + "-via-" + wname
    out, (_, _, keys, cls_of, _) = stage_two(
        top, Vsub, alive, img, trels, ttw, f"tz-{name}{sfx}", treps)
    if fast:
        cnt = [0] * len(keys)
        for c, t in zip(cls_of, treps):
            cnt[c] += t[-1]
        assert sum(cnt) == 10 * npb
        out["class_coset_counts"] = sorted(set(cnt))
        out["twist_representatives"] = len(treps)
        out["centralizer_sizes"] = csz
    out["V_order"] = len(Vsub)
    out["tietze_gens"] = len(alive)
    out["tietze_relators"] = len(trels)
    out["seconds_total"] = round(time.time() - t0)
    outp = os.path.join(HERE, f"tz-{name}{sfx}.json")
    json.dump(out, open(outp, "w"), indent=1)
    log("saved", outp)


if __name__ == "__main__":
    a = sys.argv[2:]
    main(sys.argv[1], fast="--fast" in a,
         via=[a[i + 1] for i, x in enumerate(a) if x == "--via"])
