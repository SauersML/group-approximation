"""Calibration for affine-relay-label-lifts-descend-to-two-symbols and
free-orbit-label-lifts-need-count-raising-label-automata.

Over G = C_n (exhaustive), L = {0} + B, C = {0} + B x Z/q.
tau(l)(g) = pi(l(g+1)) with pi a permutation of B (injective label automaton, memory M = {0,1}).
An affine relay: for an active output window u = (u0, u1), coefficients (a0, a1) with
a_m = 0 where u_m = 0 and a0 + a1 = 1 (integers, reduced mod q).
Checks, for random relays:
  1. theta commutes with translation and with the Z/q action, and sigma theta = tau sigma;
  2. theta is injective iff every A_l is injective mod q (tau is injective here);
  3. fibre count |F|^|l| <= |F|^|tau l| for every label configuration l (here equality, tau bijective).
"""
import itertools
import random

random.seed(20260917)


def rank_mod_p(rows, ncols, p):
    m = [list(r) for r in rows]
    rank, col = 0, 0
    while rank < len(m) and col < ncols:
        piv = next((i for i in range(rank, len(m)) if m[i][col] % p), None)
        if piv is None:
            col += 1
            continue
        m[rank], m[piv] = m[piv], m[rank]
        inv = pow(m[rank][col], p - 2, p)
        m[rank] = [(v * inv) % p for v in m[rank]]
        for i in range(len(m)):
            if i != rank and m[i][col] % p:
                f = m[i][col]
                m[i] = [(a - f * b) % p for a, b in zip(m[i], m[rank])]
        rank += 1
        col += 1
    return rank


def run(n, b, q, trials):
    B = list(range(1, b + 1))
    L = [0] + B
    C = [0] + [(x, i) for x in B for i in range(q)]
    agree = 0
    inj = 0
    for _ in range(trials):
        pi = dict(zip(B, random.sample(B, b)))
        pi[0] = 0
        coef = {}
        for u0 in L:
            for u1 in B:
                coef[(u0, u1)] = random.randint(-3, 3) if u0 else 0

        def tau(l):
            return tuple(pi[l[(g + 1) % n]] for g in range(n))

        def theta(c):
            out = []
            for g in range(n):
                c0, c1 = c[g], c[(g + 1) % n]
                u0 = c0[0] if c0 else 0
                u1 = c1[0] if c1 else 0
                if u1 == 0:
                    out.append(0)
                    continue
                a0 = coef[(u0, u1)]
                a1 = 1 - a0
                ph = (a0 * (c0[1] if c0 else 0) + a1 * c1[1]) % q
                out.append((pi[u1], ph))
            return tuple(out)

        def sig(c):
            return tuple(x[0] if x else 0 for x in c)

        imgs = set()
        for c in itertools.product(C, repeat=n):
            t = theta(c)
            imgs.add(t)
            assert sig(t) == tau(sig(c))
            sh = c[1:] + c[:1]
            assert theta(sh) == t[1:] + t[:1]
            add = tuple((x[0], (x[1] + 1) % q) if x else 0 for x in c)
            assert theta(add) == tuple((x[0], (x[1] + 1) % q) if x else 0 for x in t)
        theta_inj = len(imgs) == len(C) ** n
        all_rank = True
        for l in itertools.product(L, repeat=n):
            act = [h for h in range(n) if l[h]]
            tl = tau(l)
            assert sum(1 for v in tl if v) >= len(act)
            rows = []
            for g in range(n):
                if tl[g] == 0:
                    continue
                row = [0] * len(act)
                a0 = coef[(l[g], l[(g + 1) % n])]
                if l[g]:
                    row[act.index(g)] += a0
                row[act.index((g + 1) % n)] += 1 - a0
                rows.append(row)
            if act and rank_mod_p(rows, len(act), q) < len(act):
                all_rank = False
        assert theta_inj == all_rank, (theta_inj, all_rank)
        agree += 1
        inj += theta_inj
    return agree, inj


if __name__ == "__main__":
    for (n, b, q, t) in [(3, 1, 3, 30), (4, 1, 3, 30), (3, 2, 3, 20), (4, 1, 5, 20), (3, 3, 5, 5)]:
        r, i = run(n, b, q, t)
        print(f"n={n} b={b} q={q}: {r} relays ({i} injective), theta injective <=> all A_l injective mod q")
    print("ALL CHECKS PASSED")
