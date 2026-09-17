"""Lemma 6 certificates by corner assignment (fast, complete for fixed rank).

A Lemma 6 certificate for malnormal C is a folded ribbon graph Y of rank r whose boundary
words read closed paths in Gamma_C lying in rank-1, pairwise distinct components of
Y x Gamma_C.  Write phi(h) for the Gamma_C-vertex at which the boundary traversal of the
half-edge h starts.  Each edge e is crossed exactly twice, once per side, and by the
bounded-segment lemma (Lemma 6 of the proof file) the two lifts are off-diagonal.  So:

   sigma_e is the unique reduced path, in the TREE off-diagonal component of
   Gamma_C x Gamma_C, from P_e = (phi(e,0), phi(next(e,0))) to Q_e = (phi(next(e,1)), phi(e,1)).

Hence a certificate is determined by the rotation system plus the corner assignment phi, and
this search, a constraint problem over phi with the folding condition checked incrementally,
enumerates every Lemma 6 certificate of rank r.  Its negatives are exact.

Usage: python3 search_pairs.py <rank> <C words...>
       python3 search_pairs.py batch <rank> <n> <lo> <hi> [skip]   (seed 20260917, same C sequence
                                                                as search_genus1 / search_fatgraphs)
"""
import sys
import random
from stallings import INV, word, show, fold_subgroup, read, product_component_rank, is_malnormal, offdiag_depth, infinite_index, rank
from search_fatgraphs import shapes, rotations, faces, build_Y, component_id, primitive_root_free, random_word, inv


def offdiag_paths(C):
    """For each off-diagonal vertex P of C x C: dict Q -> reduced label of the tree path P -> Q (Q != P)."""
    n = C.nv()
    paths = {}
    for p in range(n):
        for q in range(n):
            if p == q:
                continue
            P = (p, q)
            got = {P: []}
            st = [P]
            while st:
                u = st.pop()
                for x, p2 in C.adj[u[0]].items():
                    q2 = C.adj[u[1]].get(x)
                    if q2 is None or p2 == q2:
                        continue
                    v = (p2, q2)
                    if v not in got:
                        got[v] = got[u] + [x]
                        st.append(v)
            del got[P]
            paths[P] = got
    return paths


def search_rotation(C, n, E, nxt, F, paths, first_only=True):
    m = len(E)
    nv = C.nv()
    phi = {}
    lab = [None] * m
    certs = []

    def assign(h, val, undo):
        cur = phi.get(h)
        if cur is None:
            phi[h] = val
            undo.append(h)
            return True
        return cur == val

    def folded_at(e):
        i, j = E[e]
        for v in {i, j}:
            letters = []
            for e2 in range(e + 1):
                a, b = E[e2]
                if a == v:
                    letters.append(lab[e2][0])
                if b == v:
                    letters.append(INV(lab[e2][-1]))
            if len(set(letters)) != len(letters):
                return False
        return True

    def finish():
        Y = build_Y(n, E, lab)
        if Y is None:
            return None
        comps, info = set(), []
        for f in F:
            w = []
            for (e, s) in f:
                w += lab[e] if s == 0 else inv(lab[e])
            if not primitive_root_free(w):
                return None
            e0, s0 = f[0]
            v0 = E[e0][s0]
            c = phi[f[0]]
            if read(C, c, w) != c or product_component_rank(Y, v0, C, c)[0] != 1:
                return None
            cid = component_id(Y, v0, C, c)
            if cid in comps:
                return None
            comps.add(cid)
            info.append((show(w), c))
        return (n, E, [show(x) for x in lab], info)

    def rec(e):
        if e == m:
            res = finish()
            if res:
                certs.append(res)
                return first_only
            return False
        h0, h1 = (e, 0), (e, 1)
        ka, kb, kc, kd = h0, nxt[h0], nxt[h1], h1
        a, b = phi.get(ka), phi.get(kb)
        Ps = [(a, b)] if a is not None and b is not None and a != b else \
             [P for P in paths if (a is None or P[0] == a) and (b is None or P[1] == b)]
        for P in Ps:
            if P[0] == P[1]:
                continue
            c, d = phi.get(kc), phi.get(kd)
            for Q, sig in paths[P].items():
                if (c is not None and Q[0] != c) or (d is not None and Q[1] != d):
                    continue
                undo = []
                ok = assign(ka, P[0], undo) and assign(kb, P[1], undo) and assign(kc, Q[0], undo) and assign(kd, Q[1], undo)
                if ok:
                    lab[e] = sig
                    if folded_at(e) and rec(e + 1):
                        return True
                    lab[e] = None
                for h in undo:
                    del phi[h]
        return False

    rec(0)
    return certs


def iso_shapes(r):
    """shapes(r) up to graph isomorphism (vertex relabelling); ranks 2,3,4 give 3, 12, 73 shapes."""
    import itertools
    seen, out = set(), []
    for n, E in shapes(r):
        key = min(tuple(sorted(tuple(sorted((p[i], p[j]))) for i, j in E)) for p in itertools.permutations(range(n)))
        if (n, key) not in seen:
            seen.add((n, key))
            out.append((n, E))
    return out


def search(C, r, first_only=True):
    paths = offdiag_paths(C)
    certs = []
    for n, E in iso_shapes(r):
        for rot, nxt in rotations(n, E):
            F = faces(E, nxt)
            got = search_rotation(C, n, E, nxt, F, paths, first_only)
            if got:
                certs += [g + (rot,) for g in got]
                if first_only:
                    return certs
    return certs


def genus_of(res, r):
    k = len(res[3])
    return (2 - (1 - r) - k) // 2, k


def batch(r, N, lo, hi, skip=0, seed=20260917):
    rng = random.Random(seed)
    tried = certified = 0
    seen = set()
    while tried < N:
        g1 = random_word(rng.randint(lo, hi), rng)
        g2 = random_word(rng.randint(lo, hi), rng)
        C = fold_subgroup([g1, g2])
        if rank(C) != 2 or not infinite_index(C) or not is_malnormal(C):
            continue
        key = (show(g1), show(g2))
        if key in seen:
            continue
        seen.add(key)
        tried += 1
        if tried <= skip:
            continue
        K = offdiag_depth(C)
        certs = search(C, r)
        if certs:
            certified += 1
            print("CERT", tried, key, "V", C.nv(), "K", K, "Y genus,boundaries", genus_of(certs[0], r), certs[0])
        else:
            print("NONE", tried, key, "V", C.nv(), "K", K)
        sys.stdout.flush()
    print("batch rank", r, "lengths", lo, hi, "seed", seed, "skip", skip, ":", certified, "/", tried - skip, "certified")


if __name__ == "__main__":
    if sys.argv[1] == "batch":
        batch(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]),
              int(sys.argv[6]) if len(sys.argv) > 6 else 0)
    else:
        r = int(sys.argv[1])
        C = fold_subgroup([word(g) for g in sys.argv[2:]])
        mal = is_malnormal(C)
        print("C", sys.argv[2:], "V", C.nv(), "malnormal", mal, "K", offdiag_depth(C) if mal else None, "shapes up to iso", len(iso_shapes(r)))
        if not mal:
            print("not malnormal: Lemma 6 search not complete, skipped")
            sys.exit(0)
        certs = search(C, r)
        print("certificates:", [(genus_of(c, r), c) for c in certs] if certs else "NONE (exhaustive for rank %d)" % r)
        sys.stdout.flush()
