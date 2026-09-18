#!/usr/bin/env python3
"""Brute-force regression check for orientation lifts of 2-to-1 games.

Checks, on random small weighted bipartite 2-to-1 games (left alphabet [2k],
right alphabet [k]):

  (S)  val(G)/2 <= val(U_o) <= val(G)  for every orientation o;
  (P)  Psi(U_o) is fully rich and val(U_o) <= val(Psi(U_o)) <= 2 val(U_o);
  (C)  for a random unique game U, Psi(U) with the canonical orientation has
       lift value >= val(U);
  (N)  every orientation of an F_2-linear 2-to-1 map F_2^l -> F_2^(l-1) has the
       normal form o(s) = lam(s) xor g(p(s)) with lam(ker) = 1;
  (B)  bipartite double cover B of a random non-bipartite unique game has
       val(U) <= val(B) <= 2 val(U).

Exact rational arithmetic. Bounded output is a regression check, not a proof.
"""
import itertools
import random
from fractions import Fraction


def best_right(left_lab, edges, right_alpha):
    """Value with best right labels. edges: list of (u, v, w, cons) where cons maps
    left label -> right label (projection)."""
    score = {}
    for (u, v, w, cons) in edges:
        b = cons[left_lab[u]]
        score[(v, b)] = score.get((v, b), 0) + w
    total = Fraction(0)
    rv = set(e[1] for e in edges)
    for v in rv:
        total += max(score.get((v, b), 0) for b in right_alpha)
    return total


def value(nleft, left_alpha, edges, right_alpha):
    best = Fraction(0)
    for lab in itertools.product(left_alpha, repeat=nleft):
        best = max(best, best_right(lab, edges, right_alpha))
    return best


def random_2to1(k, rng):
    labels = list(range(2 * k))
    rng.shuffle(labels)
    p = [0] * (2 * k)
    for j in range(k):
        p[labels[2 * j]] = j
        p[labels[2 * j + 1]] = j
    return tuple(p)


def all_2to1(k):
    out = set()
    for perm in itertools.permutations(range(2 * k)):
        p = [0] * (2 * k)
        for j in range(k):
            p[perm[2 * j]] = j
            p[perm[2 * j + 1]] = j
        out.add(tuple(p))
    return sorted(out)


def random_orientation(p, k, rng):
    o = [0] * len(p)
    for j in range(k):
        fib = [a for a in range(len(p)) if p[a] == j]
        bit = rng.randrange(2)
        o[fib[0]], o[fib[1]] = bit, 1 - bit
    return o


def lift(edges, orients, k):
    out = []
    for (u, v, w, cons), o in zip(edges, orients):
        out.append((u, v, w, tuple(cons[a] * 2 + o[a] for a in range(2 * k))))
    return out


def psi(edges, k):
    maps = all_2to1(k)
    out = []
    for (u, v, w, cons) in edges:
        for s in maps:
            out.append((u, (v, s), w / len(maps), tuple(s[cons[a]] for a in range(2 * k))))
    return out, maps


def pairing(cons):
    d = {}
    for a, b in enumerate(cons):
        d.setdefault(b, []).append(a)
    return frozenset(frozenset(x) for x in d.values())


def check_rich(edges, nleft, k):
    allp = set(pairing(s) for s in all_2to1(k))
    for u in range(nleft):
        law = {}
        tot = Fraction(0)
        for (uu, v, w, cons) in edges:
            if uu == u:
                law[pairing(cons)] = law.get(pairing(cons), 0) + w
                tot += w
        if tot == 0:
            continue
        vals = set(law.get(q, 0) / tot for q in allp)
        assert len(vals) == 1, "not rich"


def main():
    rng = random.Random(20260917)
    k = 2
    L, R = list(range(2 * k)), list(range(k))
    n_s = 0
    for trial in range(40):
        nleft, nright = 3, 2
        edges = []
        for u in range(nleft):
            for v in range(nright):
                if rng.random() < 0.8:
                    edges.append((u, v, Fraction(rng.randint(1, 3)), random_2to1(k, rng)))
        if not edges:
            continue
        vg = value(nleft, L, edges, R)
        for _ in range(4):
            orients = [random_orientation(c, k, rng) for (_, _, _, c) in edges]
            U = lift(edges, orients, k)
            vu = value(nleft, L, U, list(range(2 * k)))
            assert vg / 2 <= vu <= vg, ("S", vg, vu)
            P, _ = psi(U, k)
            check_rich(P, nleft, k)
            vp = value(nleft, L, P, R)
            assert vu <= vp <= 2 * vu, ("P", vu, vp)
            n_s += 1
    print("(S),(P) orientation sandwich and Psi bounds: %d lifts, 0 failures" % n_s)

    n_c = 0
    for trial in range(30):
        nleft, nright = 3, 2
        edges = []
        for u in range(nleft):
            for v in range(nright):
                if rng.random() < 0.8:
                    perm = list(range(2 * k))
                    rng.shuffle(perm)
                    edges.append((u, v, Fraction(rng.randint(1, 3)), tuple(perm)))
        if not edges:
            continue
        vU = value(nleft, L, edges, list(range(2 * k)))
        P, maps = psi(edges, k)
        orients = []
        for (u, (v, s), w, cons) in P:
            # canonical: bit = whether phi(a) is the larger element of its s-fibre
            orients.append([int(cons_phi_a == max(x for x in range(2 * k) if s[x] == s[cons_phi_a]))
                            for cons_phi_a in [dict((e[0], e[3]) for e in edges if e[1] == v)[u][a]
                                               for a in range(2 * k)]])
        UP = lift(P, orients, k)
        vlift = value(nleft, L, UP, list(range(2 * k)))
        assert vlift >= vU, ("C", vU, vlift)
        n_c += 1
    print("(C) canonical orientation of Psi(U) has lift value >= val(U): %d games, 0 failures" % n_c)

    # (N) normal form over F_2^3 -> F_2^2
    l = 3
    vecs = list(itertools.product(range(2), repeat=l))
    n_n = 0
    for trial in range(50):
        while True:
            M = [[rng.randrange(2) for _ in range(l)] for _ in range(l - 1)]
            img = set(tuple(sum(M[i][j] * x[j] for j in range(l)) % 2 for i in range(l - 1)) for x in vecs)
            if len(img) == 2 ** (l - 1):
                break
        p = {x: tuple(sum(M[i][j] * x[j] for j in range(l)) % 2 for i in range(l - 1)) for x in vecs}
        chi = [x for x in vecs if any(x) and not any(p[x])][0]
        fib = {}
        for x in vecs:
            fib.setdefault(p[x], []).append(x)
        o = {}
        for y, xs in fib.items():
            bit = rng.randrange(2)
            o[xs[0]], o[xs[1]] = bit, 1 - bit
        lam = [c for c in vecs if sum(a * b for a, b in zip(c, chi)) % 2 == 1][0]
        g = {}
        for x in vecs:
            val = o[x] ^ (sum(a * b for a, b in zip(lam, x)) % 2)
            assert g.setdefault(p[x], val) == val, "normal form fails"
        n_n += 1
    print("(N) linear orientation normal form: %d maps, 0 failures" % n_n)

    # (B) bipartite double cover
    n_b = 0
    for trial in range(30):
        n = 3
        cons = []
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.9:
                    perm = list(range(2 * k))
                    rng.shuffle(perm)
                    cons.append((i, j, Fraction(rng.randint(1, 3)), tuple(perm)))
        if not cons:
            continue
        vU = Fraction(0)
        for lab in itertools.product(L, repeat=n):
            vU = max(vU, sum(w for (i, j, w, ph) in cons if ph[lab[i]] == lab[j]))
        edges = []
        for (i, j, w, ph) in cons:
            inv = [0] * (2 * k)
            for a in range(2 * k):
                inv[ph[a]] = a
            edges.append((i, j, w / 2, ph))
            edges.append((j, i, w / 2, tuple(inv)))
        vB = value(n, L, edges, list(range(2 * k)))
        assert vU <= vB <= 2 * vU, ("B", vU, vB)
        n_b += 1
    print("(B) bipartite double cover bounds: %d games, 0 failures" % n_b)


if __name__ == "__main__":
    main()
