#!/usr/bin/env python3
"""Sanity checks for the group-theoretic lemmas in
research/artifacts/homomorphic-group-alphabet-surjunctivity-2026-09-16.md.

These checks are evidence only. The lemmas are proved in the artifact for all
finite groups. This script enumerates every homomorphism mu : K^2 -> K for
three small alphabets K and checks the following.

  Lemma 3/4: if mu is surjective, mu maps every minimal normal subgroup N
    placed in one coordinate to 1 or to a minimal normal subgroup isomorphic
    to N. In particular it preserves the abelian and nonabelian socle parts.
  Necessity of step (i): among non-surjective mu, count those violating that
    invariance.
  Lemma 6 (T nonabelian simple): the surjective mu : T^2 -> T are exactly the
    maps alpha o pi_m, with alpha in Aut(T) and m one of the two coordinates.

Permutations are tuples. compose(p, q) = p o q, meaning apply q first.
Single-threaded, runs in well under a minute.
"""
from itertools import permutations


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def closure(gens, n):
    e = tuple(range(n))
    seen = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = compose(g, s)
                if h not in seen:
                    seen.add(h)
                    new.append(h)
        frontier = new
    return seen


def order(p):
    e = tuple(range(len(p)))
    k, q = 1, p
    while q != e:
        q = compose(q, p)
        k += 1
    return k


def bfs_words(gens, n):
    """Return elements with a spanning tree: parent[g] = (h, i) with g = h * gens[i]."""
    e = tuple(range(n))
    parent = {e: None}
    orderlist = [e]
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for i, s in enumerate(gens):
                h = compose(g, s)
                if h not in parent:
                    parent[h] = (g, i)
                    orderlist.append(h)
                    new.append(h)
        frontier = new
    return orderlist, parent


def homs(K_elems, gens, n, target_elems, n_target):
    """All homomorphisms K -> target determined by images of gens, verified fully."""
    orderlist, parent = bfs_words(gens, n)
    assert set(orderlist) == set(K_elems)
    idx = {g: i for i, g in enumerate(orderlist)}
    N = len(orderlist)
    # multiplication table of K in index form
    mul = [[idx[compose(orderlist[i], orderlist[j])] for j in range(N)] for i in range(N)]
    ords = [order(s) for s in gens]
    cands = [[t for t in target_elems if order(t) in divisors(o)] for o in ords]
    e_t = tuple(range(n_target))
    out = []

    def rec(k, imgs):
        if k == len(gens):
            phi = [None] * N
            for g in orderlist:
                if parent[g] is None:
                    phi[idx[g]] = e_t
                else:
                    h, i = parent[g]
                    phi[idx[g]] = compose(phi[idx[h]], imgs[i])
            ok = True
            for i in range(N):
                pi = phi[i]
                row = mul[i]
                for j in range(N):
                    if phi[row[j]] != compose(pi, phi[j]):
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                out.append({orderlist[i]: phi[i] for i in range(N)})
            return
        for t in cands[k]:
            rec(k + 1, imgs + [t])

    rec(0, [])
    return out


def divisors(o):
    return {d for d in range(1, o + 1) if o % d == 0}


def is_even(p):
    n = len(p)
    seen = [False] * n
    parity = 0
    for i in range(n):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                L += 1
            parity ^= (L - 1) & 1
    return parity == 0


def run_case(name, n, gens, minimal_normals):
    K = closure(gens, n)
    H = homs(K, gens, n, sorted(K), n)
    print(f"[{name}] |K| = {len(K)}, #Hom(K,K) = {len(H)}")
    images = [frozenset(h.values()) for h in H]
    img_gens = [[h[g] for g in gens] for h in H]
    total = surj = violations_surj = violations_nonsurj = 0
    for a in range(len(H)):
        for b in range(len(H)):
            if not all(compose(x, y) == compose(y, x) for x in img_gens[a] for y in img_gens[b]):
                continue
            total += 1
            ia, ib = images[a], images[b]
            prod = {compose(x, y) for x in ia for y in ib}
            is_surj = len(prod) == len(K)
            if is_surj:
                surj += 1
            bad = False
            for Nname, N, is_abelian in minimal_normals:
                for h in (H[a], H[b]):
                    img = frozenset(h[x] for x in N)
                    if len(img) == 1:
                        continue
                    # must be a minimal normal subgroup of K isomorphic to N (same order suffices
                    # here since every minimal normal subgroup listed has distinct order/type)
                    if not any(img == frozenset(M) and len(M) == len(N) and ab == is_abelian
                               for _, M, ab in minimal_normals):
                        bad = True
            if bad:
                if is_surj:
                    violations_surj += 1
                else:
                    violations_nonsurj += 1
    print(f"[{name}] #Hom(K^2,K) = {total}, surjective = {surj}, "
          f"socle-invariance violations: surjective = {violations_surj}, non-surjective = {violations_nonsurj}")
    return H, total, surj, violations_surj, violations_nonsurj


def main():
    # A_5 on {0..4}: a = (0 1)(2 3), b = (1 2 4) as the image tuple (0, 2, 4, 3, 1);
    # check ab has order 5 and <a,b> = A_5
    a = (1, 0, 3, 2, 4)
    b = (0, 2, 4, 3, 1)
    A5 = closure([a, b], 5)
    assert len(A5) == 60 and order(compose(a, b)) == 5
    H, total, surj, vs, vn = run_case("A5", 5, [a, b], [("A5", sorted(A5), False)])
    assert len(H) == 121          # trivial map + 120 automorphisms
    assert total == 241 and surj == 240 and vs == 0
    # Lemma 6 for T = A_5, |M| = 2: surjective homs are alpha o pi_m (2 * |Aut A_5| = 240)

    # K = A_5 x Z/2 on 7 points; generators a*(5 6) and b
    a2 = a + (6, 5)
    b2 = b + (5, 6)
    A5x = [p + (5, 6) for p in A5]
    Z2 = [tuple(range(7)), (0, 1, 2, 3, 4, 6, 5)]
    run_case("A5xZ2", 7, [a2, b2], [("A5x1", A5x, False), ("1xZ2", Z2, True)])

    # K = S_4; unique minimal normal subgroup V_4
    s = (1, 0, 2, 3)
    c = (1, 2, 3, 0)
    V4 = [(0, 1, 2, 3), (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0)]
    run_case("S4", 4, [s, c], [("V4", V4, True)])


if __name__ == "__main__":
    main()
