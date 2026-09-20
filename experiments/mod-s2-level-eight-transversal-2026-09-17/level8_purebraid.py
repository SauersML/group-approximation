#!/usr/bin/env python3
"""Memory-light version of level8_index2.py: abelianised Reidemeister--Schreier
over K2 = PB_5/<Delta^2> = PMod(S_{0,6}) (Artin's 10-generator presentation)
instead of over H = B_5/<<Delta^2>>.  Index of M'' in K2 is 1024 (resp. 512
for Gamma(4), 1 for Gamma(2)), so the Schreier data are small.

Every relation used is checked exactly in B_5 through Artin's faithful action
on the free group F_5 (sigma_i: x_i -> x_i x_{i+1} x_i^-1, x_{i+1} -> x_i).

Completeness of the presentation: combing, PB_n = U_n x| PB_{n-1} with U_n
free on A_{1n}, ..., A_{n-1,n} and PB_{n-1} the first n-1 strands (Artin
1947; Birman, Braids, Links and Mapping Class Groups, Lemma 1.8.2 / Cor. 1.8.3).
So PB_5 is presented by the A_ij and, for every generator A_rs with s < j and
every A_ij, one relation A_rs^-1 A_ij A_rs = (a word in A_1j..A_{j-1,j});
any word verified to be correct serves.  Delta^2 is central, so adding one
word equal to Delta^2 presents K2.

Separating classes.  All separating twists of S_2 are H-conjugates of
t_s = (s1 s2)^6 (gamma4.py docstring).  g t_s g^-1 with g = k h, k in K2 and
h ranging over the 5! coset representatives, is k t_S k^-1 where t_S is the
square of a twist about a curve enclosing the 3-set S = h({1,2,3}) of
punctures from {1..5}, and PMod(S_{0,6}) is transitive on curves of a given
puncture partition.  So the distinct classes are the [k t_S k^-1], S over the
ten 3-subsets, k over K2/M''; t_S = (A_ab A_ac A_bc)^2 once A_ab A_ac A_bc is
checked to be B_5-conjugate to (s1 s2)^3 = A12 A13 A23.

Usage: python3 level8_purebraid.py N2 out.pkl       (validation, Gamma(2))
       python3 level8_purebraid.py N4 out.pkl       (validation, Gamma(4))
       python3 level8_purebraid.py f CODE out.pkl   (index-two Gamma'')
"""
import itertools
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-gamma4-torsion-census-2026-09-17"))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import gamma4 as G4  # noqa: E402
import level8_index2 as L8  # noqa: E402


# ---------------------------------------------------------------------------
# 1. B_5 words (letters +-k, k = 1..4 for sigma_k) and Artin's action on F_5.
# ---------------------------------------------------------------------------
def freduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def finv(w):
    return [-x for x in reversed(w)]


def sigma_images(k):
    """Images of x_1..x_5 under sigma_k^{+-1} (dict: generator -> word)."""
    i = abs(k)
    if k > 0:
        return {i: [i, i + 1, -i], i + 1: [i]}
    return {i: [i + 1], i + 1: [-(i + 1), i, i + 1]}


def fapply(img, w):
    out = []
    for x in w:
        y = img.get(abs(x), [abs(x)])
        out.extend(y if x > 0 else finv(y))
    return freduce(out)


def artin(word):
    """rho(word) = phi_{w1} o ... o phi_{wn}: tuple of images of x_1..x_5."""
    imgs = [[x] for x in range(1, 6)]
    for k in reversed(word):
        s = sigma_images(k)
        imgs = [fapply(s, im) for im in imgs]
    return tuple(tuple(im) for im in imgs)


def binv(w):
    return [-x for x in reversed(w)]


def same(u, v):
    return artin(u) == artin(v)


def check_braid_relations():
    for i in range(1, 4):
        assert same([i, i + 1, i], [i + 1, i, i + 1])
    for i in range(1, 5):
        for j in range(i + 2, 5):
            assert same([i, j], [j, i])
        assert artin([i, -i]) == artin([])


# ---------------------------------------------------------------------------
# 2. Artin generators A_ij and the combed presentation of PB_5.
# ---------------------------------------------------------------------------
PAIRS = [(i, j) for j in range(2, 6) for i in range(1, j)]
GID = {p: n for n, p in enumerate(PAIRS)}         # 10 generators, 0..9


def A_sigma(i, j):
    up = list(range(j - 1, i, -1))                 # sigma_{j-1} ... sigma_{i+1}
    return up + [i, i] + binv(up)


def to_sigma(aword):
    """A-word: list of (gen id, +-1)."""
    out = []
    for g, e in aword:
        w = A_sigma(*PAIRS[g])
        out.extend(w if e > 0 else binv(w))
    return out


def a(i, j, e=1):
    return (GID[(i, j)], e)


def ainv(aword):
    return [(g, -e) for g, e in reversed(aword)]


def conj_rhs(r, s, i, j):
    """Artin's word for A_rs^-1 A_ij A_rs (r < s < j, i < j)."""
    if s < i or i < r:                              # disjoint or nested
        return [a(i, j)]
    if s == i:
        return [a(r, j), a(i, j), a(r, j, -1)]
    if i == r:
        return [a(r, j), a(s, j), a(i, j), a(s, j, -1), a(r, j, -1)]
    assert r < i < s
    return [a(r, j), a(s, j), a(r, j, -1), a(s, j, -1), a(i, j),
            a(s, j), a(r, j), a(s, j, -1), a(r, j, -1)]


def pb5_relations():
    """List of (lhs, rhs) A-words, each verified in B_5."""
    rels = []
    for (r, s) in PAIRS:
        for (i, j) in PAIRS:
            if not s < j:
                continue
            lhs = [a(r, s, -1), a(i, j), a(r, s)]
            rhs = conj_rhs(r, s, i, j)
            assert all(PAIRS[g][1] == j for g, _ in rhs)
            assert same(to_sigma(lhs), to_sigma(rhs)), (r, s, i, j)
            rels.append((lhs, rhs))
    return rels


DELTA2 = [a(1, 2), a(1, 3), a(2, 3), a(1, 4), a(2, 4), a(3, 4),
          a(1, 5), a(2, 5), a(3, 5), a(4, 5)]


def check_delta2():
    assert same(to_sigma(DELTA2), [1, 2, 3, 4] * 5)


def twist3(S):
    p, q, r = S
    return [a(p, q), a(p, r), a(q, r)]


def conjugator(S, maxlen=7):
    """Shortest sigma-word w with w^-1 (s1 s2)^3 w = A_pq A_pr A_qr."""
    target = artin(to_sigma(twist3(S)))
    base = [1, 2] * 3
    assert same(base, to_sigma(twist3((1, 2, 3))))
    letters = [1, -1, 2, -2, 3, -3, 4, -4]
    seen = {artin([])}
    layer = [[]]
    for _ in range(maxlen + 1):
        for w in layer:
            if artin(binv(w) + base + w) == target:
                return w
        nxt = []
        for w in layer:
            for x in letters:
                if w and w[-1] == -x:
                    continue
                v = w + [x]
                key = artin(v)
                if key not in seen:
                    seen.add(key)
                    nxt.append(v)
        layer = nxt
    raise RuntimeError(f"no conjugator for {S}")


# conjugators found by conjugator() (shortest words); re-verified at run time
CONJ = {(1, 2, 3): [], (1, 2, 4): [-3], (1, 2, 5): [-3, -4],
        (1, 3, 4): [-3, -2], (1, 3, 5): [-3, -2, -4],
        (1, 4, 5): [-3, -2, -4, -3], (2, 3, 4): [3, 2, 1],
        (2, 3, 5): [3, 2, 1, -4], (2, 4, 5): [3, 2, 1, -4, -3],
        (3, 4, 5): [3, 2, 1, 4, 3, 2]}
TRIPLES = list(itertools.combinations(range(1, 6), 3))


def verify_all():
    check_braid_relations()
    rels = pb5_relations()
    check_delta2()
    base = [1, 2] * 3
    for S in TRIPLES:
        w = CONJ[S]
        assert same(binv(w) + base + w, to_sigma(twist3(S))), S
    return rels + [(DELTA2, [])]


# ---------------------------------------------------------------------------
# 3. Symplectic matrices and the right action of K2 on canonical objects.
# ---------------------------------------------------------------------------
def sigma_matrix(word):
    A = np.eye(4, dtype=np.int64)
    for k in word:
        x = C.CHAIN[abs(k) - 1]
        T = np.eye(4, dtype=np.int64) + (1 if k > 0 else -1) * np.outer(x, x @ C.J)
        A = A @ T
    return A


def check_matrices():
    for k in range(1, 5):
        assert (sigma_matrix([k]) == C.GENMATS[k - 1]).all()
        assert (sigma_matrix([k, -k]) == np.eye(4, dtype=np.int64)).all()


def level_setup(mode, code=None):
    if mode == "N2":
        return (lambda A: tuple(int(t) % 2 for t in A.flatten()),
                lambda key: np.array(key, dtype=np.int64).reshape(4, 4), 2)
    if mode == "N4":
        return (lambda A: G4.canon_pm(A, 4),
                lambda key: np.array(key, dtype=np.int64).reshape(4, 4), 4)
    basis = L8.sp_basis()
    canon, rep = L8.make_canon(L8.kernel_echelon(code, basis))
    return canon, rep, 8


def enumerate_K2(canon, rep, N, limit=5000):
    mats = [sigma_matrix(A_sigma(*p)) % N for p in PAIRS]
    start = canon(np.eye(4, dtype=np.int64))
    index, objs, act, reps = {start: 0}, [start], [], []
    q = 0
    while q < len(objs):
        A = rep(objs[q])
        reps.append(A)
        row = []
        for B in mats:
            nb = canon((A @ B) % N)
            if nb not in index:
                index[nb] = len(objs)
                objs.append(nb)
                if len(objs) > limit:
                    raise RuntimeError("orbit exceeds limit")
            row.append(index[nb])
        act.append(row)
        q += 1
    k = len(act)
    inv = [[None] * 10 for _ in range(k)]
    for c in range(k):
        for g in range(10):
            d = act[c][g]
            assert inv[d][g] is None, "not a permutation"
            inv[d][g] = c
    return objs, act, inv, reps


# ---------------------------------------------------------------------------
# 4. Abelianised Reidemeister--Schreier over K2 with inverse letters.
# ---------------------------------------------------------------------------
def perm_trace(act, inv, c, aword):
    for g, e in aword:
        c = act[c][g] if e > 0 else inv[c][g]
    return c


def schreier(act):
    k = len(act)
    seen = [False] * k
    seen[0] = True
    tree = set()
    queue = [0]
    for c in queue:
        for g in range(10):
            d = act[c][g]
            if not seen[d]:
                seen[d] = True
                tree.add((c, g))
                queue.append(d)
    assert all(seen)
    gen = {}
    for c in range(k):
        for g in range(10):
            if (c, g) not in tree:
                gen[(c, g)] = len(gen)
    return gen


def trace(act, inv, gen, c, aword, vec, sign=1):
    """Adds sign * [path_c aword path_{c.aword}^-1] to vec; returns end."""
    for g, e in aword:
        if e > 0:
            x = gen.get((c, g))
            if x is not None:
                vec[x] = vec.get(x, 0) + sign
            c = act[c][g]
        else:
            c = inv[c][g]
            x = gen.get((c, g))
            if x is not None:
                vec[x] = vec.get(x, 0) - sign
    return c


def reduce_mode(mode, code=None):
    t0 = time.time()
    rels = verify_all()
    check_matrices()
    canon, rep, N = level_setup(mode, code)
    objs, act, inv, reps = enumerate_K2(canon, rep, N)
    k = len(act)
    for lhs, rhs in rels:
        for c in range(k):
            assert perm_trace(act, inv, c, lhs) == perm_trace(act, inv, c, rhs)
    tS = {S: twist3(S) * 2 for S in TRIPLES}
    for S in TRIPLES:
        for c in range(k):
            assert perm_trace(act, inv, c, tS[S]) == c
    gen = schreier(act)
    R = []
    for lhs, rhs in rels:
        for c in range(k):
            vec = {}
            e1 = trace(act, inv, gen, c, lhs, vec, 1)
            e2 = trace(act, inv, gen, c, rhs, vec, -1)
            assert e1 == e2
            vec = {x: y for x, y in vec.items() if y}
            if vec:
                R.append(vec)
    V, O = [], []
    winv = {S: sigma_matrix(binv(CONJ[S])) for S in TRIPLES}
    for c in range(k):
        for S in TRIPLES:
            vec = {}
            assert trace(act, inv, gen, c, tS[S], vec) == c
            V.append({x: y for x, y in vec.items() if y})
            M = (reps[c] @ winv[S]) % N
            O.append((tuple(int(t) for t in M.flatten()), S))
    print(f"{mode} {code}: cosets {k}, Schreier gens {len(gen)}, relators "
          f"{len(R)} [{time.time()-t0:.1f}s]", flush=True)
    cols, R2, V2 = C.unit_eliminate(len(gen), R, V)
    print(f"  after unit elimination: {len(cols)} gens, {len(R2)} relators "
          f"[{time.time()-t0:.1f}s]", flush=True)
    distinct = {}
    for v in V2:
        key = tuple(sorted(v.items()))
        distinct[key] = distinct.get(key, 0) + 1
    keys = list(distinct)
    kidx = {kk: i for i, kk in enumerate(keys)}
    coset_key = [kidx[tuple(sorted(v.items()))] for v in V2]
    print(f"  distinct reduced v vectors: {len(keys)}", flush=True)
    return {"f": code, "mode": mode, "cosets_in_K2": k, "cols": cols,
            "R": R2, "V": [dict(kk) for kk in keys],
            "mult": [distinct[kk] for kk in keys], "objs": O,
            "coset_key": coset_key}


if __name__ == "__main__":
    if sys.argv[1] == "f":
        d = reduce_mode("f", int(sys.argv[2]))
        out = sys.argv[3]
    else:
        d = reduce_mode(sys.argv[1])
        out = sys.argv[2]
    with open(out, "wb") as fh:
        pickle.dump(d, fh)
    print("saved", out)
