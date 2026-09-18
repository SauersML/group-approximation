#!/usr/bin/env python3
"""Checks for list-star-coherent-selector-witnesses-put-np-in-rp.

Part A  Theorem CL, toy runs of the unchanged decoder against planted LISTS of
        good outer labellings, with each seed star (w,a) predicted by its own
        list member.  Exact (no sampling) computation of the per-vertex output
        laws.  Checks, in every trial:
          (A1) P := Pr_nu[max_j beta^j >= g'/2] >= g'        (Step 1)
          (A2) E_nuA Q >= P 2^-l g'^2/4 >= p = g'^3 2^(-l-2) (Steps 2-3)
          (A3) sum_j E q^j >= E Q                            (union bound)
          (A4) max_j E_rho q^j >= p/(K L)                    (pigeonhole)
          (A5) E val(hat lambda) >= (E_rho q^{j*})^2 - 2 eps  (Step 4)
        and the lift-level Step 1 inequality
          (A0) max_j beta^j >= Pr[T] - min_j Pr[X_j] - 1/2   per star.
Part B  Theorem M mixture (rank l+1 kernel, rank-split branches x, y = x+z).
        (B1) exact DKKMS law: Pr[z|L' = 0] <= 2^(1-l) for every d' >= l-1;
        (B2) image model, exact enumeration l = 2,3,4: value, single-reference
             dishonest mass (large) and cross-branch dishonest mass chi
             (<= 2^(1-l)).
Part C  Theorem LS defect-line mixture (rank l+s kernel).
        (C1) image model, exact enumeration (l,s) in (3,1),(3,2),(3,3),(4,1):
             chi <= (2^s-1)(2^l-1) 2^-(2l+s-2) < 2^(2-l);
        (C2) seeded Monte Carlo for s = l = 5,6,7: chi 2^(l-2) <= 1 (+5 sigma).
Part D  Seed-form vacuity: on the image model with n = l+1, the 2^(l+1) kernel
        branches cover every generic seed label, so List-Seed with t = 2^(l+1)
        references holds with zero uncovered mass while the seed-form loss
        t * kappa = 2^(l+1)/(2^l - 1) exceeds 2 > gamma.

Exit status 0 iff every check passes.
"""
import itertools
import random
import sys
from fractions import Fraction as Fr

FAIL = []


def check(ok, msg):
    if not ok:
        FAIL.append(msg)
        print("FAIL:", msg)


def dot(a, b):
    return bin(a & b).count("1") & 1


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {w ^ v for w in s}
    return s


def indep(vecs):
    return len(span(vecs)) == 2 ** len(vecs)


# ---------------------------------------------------------------- Part A
def part_a0(trials=400, seed=1):
    """Lift-level Step 1: on a star, G(h,x) = ev(x) on T subset Sat, and
    X_j = {x in Sat : ev(x) != <lam_j, x>}.  Then
    max_j beta^j >= Pr[T] - min_j Pr[X_j] - 1/2."""
    rng = random.Random(seed)
    m = 4
    xs = list(range(2 ** m))
    worst = 1.0
    for _ in range(trials):
        L = rng.randint(1, 5)
        lams = [rng.randrange(2 ** m) for _ in range(L)]
        sat = {x for x in xs if rng.random() < 0.8}
        T = {x for x in sat if rng.random() < 0.8}
        ev = {x: rng.randrange(2) for x in xs}
        # ev agrees with a random list member on a random part of the star
        for x in xs:
            if rng.random() < 0.6:
                ev[x] = dot(lams[rng.randrange(L)], x)
        G = {x: (ev[x] if x in T else rng.randrange(2)) for x in xs}
        n = len(xs)
        beta = [sum(G[x] == dot(lj, x) for x in xs) / n - 0.5 for lj in lams]
        PX = [sum(1 for x in sat if ev[x] != dot(lj, x)) / n for lj in lams]
        slack = max(beta) - (len(T) / n - min(PX) - 0.5)
        worst = min(worst, slack)
        check(slack >= -1e-12, "A0 star inequality")
    print(f"A0: {trials} random stars, min slack of max_j beta^j >= "
          f"Pr[T]-min_j Pr[X_j]-1/2 is {worst:.4f} (>= 0)")


def decode_star(g_row, m, thr):
    """Decoder steps 3-5 for one guessed seed label: g_row[x] in {0,1}.
    Returns the output law as a dict alpha -> prob (empty list -> label 0)."""
    n = 2 ** m
    F = [(-1) ** g_row[x] for x in range(n)]
    Lam = [a for a in range(n)
           if sum(F[x] * (-1) ** dot(a, x) for x in range(n)) / n >= thr]
    if not Lam:
        return {0: 1.0}
    return {a: 1.0 / len(Lam) for a in Lam}


def part_a(trials=60, seed=2):
    rng = random.Random(seed)
    m, l = 3, 2            # directions F_2^3, seed alphabet 2^l = 4
    S = 2 ** l
    nA, nB, nW = 6, 3, 4
    n = 2 ** m
    ok_trials = 0
    for t in range(trials):
        L = rng.randint(1, 4)
        # outer game: A-labels alpha in F_2^m, pi(alpha) = alpha & 1
        adj = {a: rng.sample(range(nB), 2) for a in range(nA)}
        rho = [(a, b, 1.0 / (2 * nA)) for a in range(nA) for b in adj[a]]
        rhoB = {b: sum(wt for (a, bb, wt) in rho if bb == b) for b in range(nB)}
        tbits = [rng.randrange(2) for _ in range(L)]
        lam = [[(rng.randrange(2 ** (m - 1)) << 1) | tbits[j]
                for a in range(nA)] for j in range(L)]
        # corrupt one A-label of one member to make eps > 0
        jc, ac = rng.randrange(L), rng.randrange(nA)
        lam[jc][ac] ^= 1
        vals = []
        for j in range(L):
            vals.append(sum(wt for (a, b, wt) in rho
                            if (lam[j][a] & 1) == tbits[j]))
        eps = 1 - min(vals)
        # seeds and predictors
        h = [rng.randrange(S) for _ in range(nW)]
        star = {}
        for w in range(nW):
            for a in range(nA):
                j = rng.randrange(L)
                noise = rng.choice([0, 0, 1, 2, 3])
                flips = set(rng.sample(range(n), noise))
                rows = []
                for s in range(S):
                    if s == h[w]:
                        row = [dot(lam[j][a], x) ^ (x in flips)
                               for x in range(n)]
                    elif rng.random() < 0.5:
                        dec = rng.randrange(n)       # adversarial linear decoy
                        row = [dot(dec, x) for x in range(n)]
                    else:
                        row = [rng.randrange(2) for x in range(n)]
                    rows.append(row)
                star[(w, a)] = rows
        nu = 1.0 / (nW * nA)
        # Step 1 quantities
        mb = {}
        for (w, a), rows in star.items():
            mb[(w, a)] = max(sum(rows[h[w]][x] == dot(lam[j][a], x)
                                 for x in range(n)) / n - 0.5
                             for j in range(L))
        gp = sum(mb.values()) * nu
        if gp <= 0:
            continue
        P = sum(nu for v in mb.values() if v >= gp / 2 - 1e-12)
        check(P >= gp - 1e-12, f"A1 trial {t}")
        # exact output laws
        law = {}
        for a in range(nA):
            d = {}
            for w in range(nW):
                for s in range(S):
                    for al, pr in decode_star(star[(w, a)][s], m,
                                              gp / 2).items():
                        d[al] = d.get(al, 0.0) + pr / (nW * S)
            law[a] = d
        Q = [sum(law[a].get(al, 0.0) for al in set(lam[j][a] for j in range(L)))
             for a in range(nA)]
        EQ = sum(Q) / nA
        p = gp ** 3 * 2 ** (-l - 2)
        check(EQ >= P * 2 ** (-l) * gp ** 2 / 4 - 1e-12, f"A2a trial {t}")
        check(EQ >= p - 1e-12, f"A2b trial {t}")
        Eq = [sum(law[a].get(lam[j][a], 0.0) for a in range(nA)) / nA
              for j in range(L)]
        check(sum(Eq) >= EQ - 1e-12, f"A3 trial {t}")
        jstar = max(range(L), key=lambda j: Eq[j])
        check(Eq[jstar] >= p / L - 1e-12, f"A4 trial {t}")
        # exact expected outer value of the decoded labelling
        EV = 0.0
        for b in range(nB):
            nbr = [(a, wt / rhoB[b]) for (a, bb, wt) in rho if bb == b]
            for (a, pa) in nbr:
                for (a2, pa2) in nbr:
                    if a == a2:
                        pr = 1.0
                    else:
                        pr = sum(law[a].get(x, 0) * law[a2].get(y, 0)
                                 for x in law[a] for y in law[a2]
                                 if (x & 1) == (y & 1))
                    EV += rhoB[b] * pa * pa2 * pr
        check(EV >= Eq[jstar] ** 2 - 2 * eps - 1e-12, f"A5 trial {t}")
        ok_trials += 1
    print(f"A1-A5: {ok_trials} toy list instances (L = 1..4, eps > 0, decoys)"
          f" checked")


# ---------------------------------------------------------------- Part B
def part_b1():
    worst = Fr(0)
    for l in range(2, 13):
        for dp in range(l - 1, 40):
            pr = Fr(1)
            for i in range(l - 1):
                pr *= Fr(2 ** (dp - 1) - 2 ** i, 2 ** dp - 2 ** i)
            check(pr <= Fr(2, 2 ** l), f"B1 l={l} d'={dp}")
            worst = max(worst, pr * 2 ** (l - 1))
    print(f"B1: exact Pr[z|L'=0] * 2^(l-1) <= {float(worst):.4f} <= 1 "
          f"for l = 2..12, d' = l-1..39")


def image_stats(l, n, branch, first_ok=None):
    """Exact enumeration of the image model: u_1..u_l iid uniform in F_2^n,
    W = span(u_1..u_(l-1)), W~ = W + <u_l>.  branch(vecs, spanset) returns
    the branch functional (bitmask f, f(v) = <f,v>) of the vertex whose
    image basis is vecs.  Returns exact fractions:
      val   = Pr[satisfied]
      chi   = Pr[satisfied and (fA ^ fB)(u_l) = 1]   (B-branch reference)
      dstar = E_W min_{psi in branches} Pr_u[sat and fA(u_l) != psi(u_l)]
      d1    = min_psi Pr[sat and fA(u_l) != psi(u_l)], psi over all of F_2^n."""
    N = 2 ** n
    tot = Fr(0)
    sat_cnt = chi_cnt = 0
    dstar_num = 0
    pair_cnt = {}
    branches = set()
    stars = []
    for pre in itertools.product(range(N), repeat=l - 1):
        W = span(pre)
        fB = branch(list(pre), W)
        rows = []
        for u in range(N):
            vecs = list(pre) + [u]
            Wt = W | {w ^ u for w in W}
            fA = branch(vecs, Wt)
            g = fA ^ fB
            if any(dot(g, v) for v in pre):
                continue
            sat_cnt += 1
            chi_cnt += dot(g, u)
            rows.append((fA, u))
            pair_cnt[(fA, u)] = pair_cnt.get((fA, u), 0) + 1
        stars.append(rows)
        branches.add(fB)
    for rows in stars:
        for (fA, u) in rows:
            branches.add(fA)
    for rows in stars:
        dstar_num += min(sum(dot(fA, u) != dot(psi, u) for (fA, u) in rows)
                         for psi in branches)
    den = N ** l
    return (Fr(sat_cnt, den), Fr(chi_cnt, den), Fr(dstar_num, den),
            Fr(min(sum(c for (fA, u), c in pair_cnt.items()
                       if dot(fA, u) != dot(psi, u)) for psi in range(N)),
               den), len(branches))


def part_b2():
    for l in (2, 3, 4):
        n = l + 1
        phim = (1 << l) - 1
        zm = 1 << l

        def br(vecs, _S, phim=phim, zm=zm):
            return 0 if indep([v & phim for v in vecs]) else zm
        val, chi, dst, d1, nb = image_stats(l, n, br)
        print(f"B2: Theorem M image model l={l}: val={float(val):.4f} "
              f"single-ref D_1={float(d1):.4f} star D_2={float(dst):.4f} "
              f"chi={float(chi):.4f} bound 2^(1-l)={2 ** (1 - l):.4f} "
              f"branches={nb}")
        check(dst <= chi, f"B2 D_star <= chi l={l}")
        check(chi <= Fr(2, 2 ** l), f"B2 chi bound l={l}")


def part_b3():
    """Exact DKKMS law, Theorem M: on a clean surjective V the y-reference
    has ev-dishonest satisfied mass exactly b(1-c)/2, while val >= 1 - bc.
    So val - 1/2 - D(h, lambda_y) >= 1/2 - b(1+c)/2 > 1/2 - 3b/4."""
    for l in (3, 4, 5, 7, 10, 20):
        k = 4 * l
        for dp in (k, 2 * k):
            b = Fr(1)
            for i in range(l - 1):
                b *= Fr(2 ** l - 2 ** i, 2 ** l) / Fr(2 ** dp - 2 ** i, 2 ** dp)
            c = Fr(2 ** (3 * k - 1) - 2 ** (l - 1 + k),
                   2 ** (3 * k) - 2 ** (l - 1 + k))
            # direct count of x in X_U minus (L'+H_U) with phi(Phi x) outside
            # phi(L') and z(x) = 1:  (1/4) 2^(3k) / (2^(3k) - 2^(l-1+k))
            pz = Fr(2 ** (3 * k - 2), 2 ** (3 * k) - 2 ** (l - 1 + k))
            check(pz == (1 - c) / 2, f"B3 count identity l={l}")
            Dy = b * pz
            gap = Fr(1, 2) - b * c - Dy
            if dp == k:
                print(f"B3: Theorem M exact, l={l} k={k} d'={dp}: b={float(b):.4f}"
                      f" c={float(c):.6f} D(h,lambda_y)={float(Dy):.4f} "
                      f"(1/2 - bc) - D = {float(gap):.4f}")
            if l >= 4:
                check(gap > 0, f"B3 single-ref margin l={l}")


# ---------------------------------------------------------------- Part C
def ls_branch(l):
    phim = (1 << l) - 1

    def br(_vecs, S):
        c = [v for v in S if v and not (v & phim)]
        # c(S) one-dimensional <(0,d)>: branch y_d, functional <d, zeta(.)>,
        # whose bitmask is (0,d) itself; otherwise branch x (functional 0)
        return c[0] if len(c) == 1 else 0
    return br


def ls_bound(l, s):
    return Fr((2 ** s - 1) * (2 ** l - 1), 2 ** (2 * l + s - 2))


def part_c1():
    for (l, s) in ((3, 1), (3, 2), (3, 3), (4, 1)):
        val, chi, dst, d1, nb = image_stats(l, l + s, ls_branch(l))
        bd = ls_bound(l, s)
        print(f"C1: Theorem LS image model (l,s)=({l},{s}): val={float(val):.4f}"
              f" single-ref D_1={float(d1):.4f} star D_(2^s)={float(dst):.4f}"
              f" chi={float(chi):.4f} union bound={float(bd):.4f} "
              f"2^(2-l)={2 ** (2 - l):.4f} branches={nb}")
        check(dst <= chi, f"C1 D_star <= chi {(l, s)}")
        check(chi <= bd, f"C1 chi <= union bound {(l, s)}")
        check(bd < Fr(4, 2 ** l), f"C1 union bound < 2^(2-l) {(l, s)}")


def part_c2(samples=30000, seed=3):
    rng = random.Random(seed)
    for l in (5, 6, 7):
        s = l
        n = l + s
        br = ls_branch(l)
        sat = chi = 0
        dref = [0] * (2 ** s)          # single references x (d=0) and y_d
        for _ in range(samples):
            us = [rng.randrange(2 ** n) for _ in range(l)]
            W = span(us[:-1])
            Wt = W | {w ^ us[-1] for w in W}
            fA = br(us, Wt)
            g = br(us[:-1], W) ^ fA
            if any(dot(g, v) for v in us[:-1]):
                continue
            sat += 1
            chi += dot(g, us[-1])
            for d in range(2 ** s):
                dref[d] += dot(fA, us[-1]) != dot(d << l, us[-1])
        best = min(dref) / samples
        print(f"C2:   single-branch references: min_d D(h, y_d or x) ~ "
              f"{best:.4f} vs val - 1/2 ~ {sat / samples - 0.5:.4f}")
        check(best > sat / samples - 0.5 - 5 * (0.25 / samples) ** 0.5
              if l >= 7 else True, f"C2 single-ref escape l={l}")
        bd = float(ls_bound(l, s))
        est = chi / samples
        tol = bd + 5 * (bd / samples) ** 0.5
        print(f"C2: Theorem LS Monte Carlo s=l={l}: val~{sat / samples:.4f} "
              f"chi~{est:.5f} bound={bd:.5f} (chi*2^(l-2)~{est * 2 ** (l - 2):.3f})")
        check(est <= tol, f"C2 chi bound l={l}")


# ---------------------------------------------------------------- Part D
def part_d():
    for l in (2, 3, 4):
        n = l + 1
        gen = cov = 0
        for pre in itertools.product(range(2 ** n), repeat=l - 1):
            if not indep(list(pre)):
                continue
            gen += 1
            restr = {tuple(dot(c, v) for v in pre) for c in range(2 ** n)}
            cov += len(restr) == 2 ** (l - 1)
        kappa = Fr(1, 2 ** l - 1)
        loss = 2 ** (l + 1) * kappa
        print(f"D: l={l}: {cov}/{gen} generic seeds have every label honest for"
              f" one of the 2^(l+1) kernel branches; seed-form loss t*kappa ="
              f" {float(loss):.3f}")
        check(cov == gen, f"D coverage l={l}")
        check(loss > 2, f"D loss l={l}")


if __name__ == "__main__":
    part_a0()
    part_a()
    part_b1()
    part_b2()
    part_b3()
    part_c1()
    part_c2()
    part_d()
    if FAIL:
        print(f"{len(FAIL)} FAILURES")
        sys.exit(1)
    print("ALL CHECKS PASS")
