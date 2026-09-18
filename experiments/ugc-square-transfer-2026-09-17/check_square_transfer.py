#!/usr/bin/env python3
"""Brute-force check of Theorem Q (dense-link square transfer).

Setting: a 2-to-1 game G with right vertices q (law nu), stars star(q) of edges
e = (p_e, pi_e), right alphabet [t], left alphabet [2t].  A symmetric coupling
J_q on star(q) x star(q) with marginals mu_q and alpha-density
J_q(e1,e2) >= alpha mu_q(e1) mu_q(e2) for e1 != e2.  The square H = Sq_J(G) has
2-to-2 constraints (e1,e2) at q.  A selection kappa picks, for each pair and each
block tau, a bit: m(sigma1) = the sigma2 in pi_e2^{-1}(tau) with
r_e2(sigma2) = r_e1(sigma1) xor kappa.

Checked, for every instance and every labelling A of the left vertices:
  (Q)  the pivot orientation o(kappa) and the B-labels built in the proof give
       val_{U_o}(A, B) >= 1 - 13 xi(A) / alpha^3, where xi(A) = 1 - val_{U_kappa}(A);
  (Q') for the induced selection kappa(o) of a random orientation o,
       opt(U_kappa(o)) >= 1 - 2 (1 - opt(U_o)).
Exit status 0 iff every check passes.
"""
import itertools
import random
import sys


def make_instance(rng, nP, nQ, star, t, coupling):
    P = list(range(nP))
    Q = list(range(nQ))
    nu = [1.0 / nQ] * nQ
    stars = {}
    for q in Q:
        edges = []
        for _ in range(star):
            p = rng.choice(P)
            # random 2-to-1 map [2t] -> [t]
            labs = list(range(2 * t))
            rng.shuffle(labs)
            pi = [0] * (2 * t)
            for i, s in enumerate(labs):
                pi[s] = i // 2
            edges.append((p, pi))
        w = [rng.randint(1, 3) for _ in range(star)]
        tot = float(sum(w))
        mu = [x / tot for x in w]
        stars[q] = (edges, mu)
    J = {}
    alpha = {}
    for q in Q:
        edges, mu = stars[q]
        n = len(edges)
        if coupling == "product":
            Jq = {(i, j): mu[i] * mu[j] for i in range(n) for j in range(n)}
        elif coupling == "offdiag":
            z = 1.0 - sum(m * m for m in mu)
            Jq = {(i, j): mu[i] * mu[j] / z for i in range(n) for j in range(n) if i != j}
            # rebalance to exact marginals mu: offdiag with product weights has
            # marginal mu_i (1 - mu_i)/z, so mix in the diagonal to fix it.
            for i in range(n):
                Jq[(i, i)] = mu[i] - sum(Jq[(i, j)] for j in range(n) if j != i)
                if Jq[(i, i)] < -1e-12:
                    raise ValueError
                if Jq[(i, i)] <= 1e-15:
                    del Jq[(i, i)]
        else:  # random symmetric dense coupling: mixture of product and a random symmetric plan
            lam = rng.uniform(0.2, 0.9)
            Jq = {(i, j): lam * mu[i] * mu[j] for i in range(n) for j in range(n)}
            # add (1-lam) * a symmetric permutation-type plan with marginals mu:
            # use the diagonal plan (e,e) with mass mu_e, which is symmetric
            for i in range(n):
                Jq[(i, i)] += (1 - lam) * mu[i]
        a = min(Jq.get((i, j), 0.0) / (mu[i] * mu[j]) for i in range(n) for j in range(n) if i != j) if n > 1 else 1.0
        J[q] = Jq
        alpha[q] = a
    return P, Q, nu, stars, J, min(1.0, min(alpha.values()))


def ref(pi, sigma):
    """reference bit r_e(sigma): 0 for the smaller element of its fibre."""
    other = [s for s in range(len(pi)) if pi[s] == pi[sigma] and s != sigma][0]
    return 0 if sigma < other else 1


def fibre_elem(pi, tau, bit):
    f = sorted(s for s in range(len(pi)) if pi[s] == tau)
    return f[bit]


def val_Uc(A, Q, nu, stars, J, kappa):
    tot = 0.0
    for q in Q:
        edges, _ = stars[q]
        for (i, j), w in J[q].items():
            (p1, pi1), (p2, pi2) = edges[i], edges[j]
            s1, s2 = A[p1], A[p2]
            tau = pi1[s1]
            if pi2[s2] != tau:
                continue
            if ref(pi2, s2) == ref(pi1, s1) ^ kappa[q][(i, j)][tau]:
                tot += nu[q] * w
    return tot


def val_Uo_best(A, Q, nu, stars, o, t):
    tot = 0.0
    for q in Q:
        edges, mu = stars[q]
        best = 0.0
        for tau in range(t):
            for b in (0, 1):
                v = sum(mu[i] for i, (p, pi) in enumerate(edges)
                        if pi[A[p]] == tau and o[q][i][A[p]] == b)
                best = max(best, v)
        tot += nu[q] * best
    return tot


def pivot_orientation(Q, stars, J, kappa, t):
    """The Theorem Q map kappa -> o.  o[q][i][sigma] in {0,1}."""
    o = {}
    for q in Q:
        edges, mu = stars[q]
        n = len(edges)
        g = {}
        for tau in range(t):
            kb = lambda i, j: 0 if i == j else kappa[q][(i, j)][tau]
            best, bestg = -1.0, None
            for es in range(n):
                cand = [kb(es, e) for e in range(n)]
                v = sum(w for (i, j), w in J[q].items() if cand[i] ^ cand[j] == kb(i, j))
                if v > best + 1e-15:
                    best, bestg = v, cand
            g[tau] = bestg
        o[q] = [[ref(pi, s) ^ g[pi[s]][i] for s in range(2 * t)] for i, (p, pi) in enumerate(edges)]
    return o


def induced_selection(Q, stars, J, o, t):
    kappa = {}
    for q in Q:
        edges, _ = stars[q]
        kappa[q] = {}
        for (i, j) in J[q]:
            pi1, pi2 = edges[i][1], edges[j][1]
            kappa[q][(i, j)] = {}
            for tau in range(t):
                s1 = fibre_elem(pi1, tau, 0)
                # m(s1) = the s2 in fibre with o2(s2) = o1(s1)
                s2 = [s for s in range(2 * t) if pi2[s] == tau and o[q][j][s] == o[q][i][s1]][0]
                kappa[q][(i, j)][tau] = ref(pi2, s2) ^ ref(pi1, s1)
    return kappa


def main():
    rng = random.Random(20260918)
    checks = 0
    worst = 0.0
    for trial in range(3000):
        coupling = ["product", "offdiag", "mixed"][trial % 3]
        nP = rng.randint(2, 4)
        nQ = rng.randint(1, 2)
        star = rng.randint(2, 5)
        t = 2
        try:
            P, Q, nu, stars, J, alpha = make_instance(rng, nP, nQ, star, t, coupling)
        except ValueError:
            continue
        # selection: planted from a random orientation, then noise
        o0 = {q: [[rng.randint(0, 1) for _ in range(2 * t)] for _ in stars[q][0]] for q in Q}
        for q in Q:
            for i, (p, pi) in enumerate(stars[q][0]):
                for tau in range(t):
                    f = [s for s in range(2 * t) if pi[s] == tau]
                    o0[q][i][f[1]] = 1 - o0[q][i][f[0]]
        kappa = induced_selection(Q, stars, J, o0, t)
        noise = rng.choice([0.0, 0.05, 0.2, 0.5])
        for q in Q:
            for key in kappa[q]:
                for tau in range(t):
                    if rng.random() < noise:
                        kappa[q][key][tau] ^= 1
        o = pivot_orientation(Q, stars, J, kappa, t)
        for A in itertools.product(range(2 * t), repeat=nP):
            xi = 1.0 - val_Uc(A, Q, nu, stars, J, kappa)
            vo = val_Uo_best(A, Q, nu, stars, o, t)
            bound = 1.0 - 13.0 * xi / alpha ** 3
            checks += 1
            if vo < bound - 1e-9:
                print("FAIL (Q)", trial, coupling, A, xi, vo, bound)
                return 1
            if xi < 0.1:
                worst = max(worst, (1 - vo) / max(xi, 1e-12) * alpha ** 3 if xi > 0 else 0.0)
        # converse (Q') for a random orientation
        orand = {q: [[0] * (2 * t) for _ in stars[q][0]] for q in Q}
        for q in Q:
            for i, (p, pi) in enumerate(stars[q][0]):
                for tau in range(t):
                    f = [s for s in range(2 * t) if pi[s] == tau]
                    b = rng.randint(0, 1)
                    orand[q][i][f[0]], orand[q][i][f[1]] = b, 1 - b
        kc = induced_selection(Q, stars, J, orand, t)
        opt_o = max(val_Uo_best(A, Q, nu, stars, orand, t) for A in itertools.product(range(2 * t), repeat=nP))
        opt_c = max(val_Uc(A, Q, nu, stars, J, kc) for A in itertools.product(range(2 * t), repeat=nP))
        checks += 1
        if opt_c < 1 - 2 * (1 - opt_o) - 1e-9:
            print("FAIL (Q')", trial, opt_c, opt_o)
            return 1
    print(f"all {checks} checks pass; worst observed alpha^3 (1-val_o)/xi at xi<0.1: {worst:.3f} (bound 13)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
