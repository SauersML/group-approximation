#!/usr/bin/env python3
"""High-advantage selector decoding, toy end-to-end check.

Checks Theorem 3 of research/high-advantage-selector-witnesses-decode-good-outer-labellings.md
on random toy composed instances in the regime that Theorem 1 of
efficient-branch-selectors-list-decode-honest-outer-labels cannot reach: outer
violation eps up to about 1/6 (realized), far above p^2 ~ 2^(-2l).

Setup per trial.
  * Outer projection game on NA x NB with a planted labelling lam of violation eps.
  * rho_A is the A-marginal of the outer edge law; the inner annotation law nu_A
    is set equal to rho_A (hypothesis (M=)).
  * Each A-vertex a has 3 seeds w.  Directions x_e are uniform on a support that
    misses a tau <= 1/16 fraction of F_2^m.
  * Predictor tables g(s, x) for s in Sigma_w (|Sigma_w| = 2^l).  At the honest
    seed label: good a's predict <lam_a, x> except for a noise fraction; bad a's
    are random.  At every other seed label an adversarial decoy linear form.
Decoder: exactly as Step 0 of the Theorem 1 proof but with list threshold 1/8.
Checked, exactly (no sampling of the decoder coins):
  (i)   list size <= 64;
  (ii)  q_a >= p0 = 2^(-l)/192 for every a with Pr[prediction correct | a] >= 3/4;
  (iii) E val(decoded) >= E[q_a q_a' 1{a,a' good, C, D}] >= p0^2 (1 - 2 eps - 2 rho_A(Bad)).
Also records how often Theorem 1's bound p^2 - 2 eps is negative (so useless).
"""
import random


def dot(a, x):
    return bin(a & x).count("1") & 1


def fourier(Fvals, m):
    n = 1 << m
    return [sum(Fvals[x] * (1 - 2 * dot(a, x)) for x in range(n)) / n for a in range(n)]


def app(M, v):
    return sum(dot(r, v) << i for i, r in enumerate(M))


def trial(rng):
    m, mp, l = 5, 3, 2
    n = 1 << m
    NA, NB, deg = 12, 6, 4
    eps_target = rng.choice([0.0, 1 / 32, 1 / 16])
    lam = [rng.randrange(1, n) for _ in range(NA)]
    lamB = [rng.randrange(1 << mp) for _ in range(NB)]
    proj, outer = {}, []
    for b in range(NB):
        for a in rng.sample(range(NA), deg):
            target = lamB[b] if rng.random() >= eps_target else rng.randrange(1 << mp)
            fix = next(v for v in range(n) if dot(v, lam[a]) == 1)
            M = []
            for i in range(mp):
                r = rng.randrange(n)
                if dot(r, lam[a]) != (target >> i) & 1:
                    r ^= fix
                M.append(r)
            proj[(a, b)] = M
            outer.append((a, b))
    E = len(outer)
    viol = sum(app(proj[e], lam[e[0]]) != lamB[e[1]] for e in outer) / E
    rhoA = [sum(1 for (aa, _) in outer if aa == a) / E for a in range(NA)]
    # inner annotation: 3 seeds per a, direction support missing tau fraction
    bad_a = set(a for a in range(NA) if rng.random() < 0.15)
    q, corr = [], []
    list_max = 0
    for a in range(NA):
        tot, cor = 0.0, 0.0
        for j in range(3):
            missing = set(rng.sample(range(n), rng.randrange(0, n // 16 + 1)))
            supp = [x for x in range(n) if x not in missing]
            s_h = rng.randrange(1 << l)
            noise = rng.choice([0.0, 0.05, 0.15]) if a not in bad_a else 0.5
            table = {}
            for s in range(1 << l):
                decoy = rng.randrange(n)
                for x in supp:
                    if s == s_h:
                        truth = dot(lam[a], x)
                        table[(s, x)] = truth ^ (1 if rng.random() < noise else 0)
                    else:
                        table[(s, x)] = dot(decoy ^ s, x)
            cor += sum(table[(s_h, x)] == dot(lam[a], x) for x in supp) / len(supp)
            for s in range(1 << l):
                Fv = [0.0] * n
                for x in supp:  # F(x) = E[(-1)^g | w, a, x]; F = 0 off the support
                    Fv[x] = 1 - 2 * table[(s, x)]
                hat = fourier(Fv, m)
                Lst = [al for al in range(n) if hat[al] >= 1 / 8]
                list_max = max(list_max, len(Lst))
                if lam[a] in Lst:
                    tot += 1 / len(Lst)
        q.append(tot / (3 * (1 << l)))
        corr.append(cor / 3)
    good = [corr[a] >= 0.75 for a in range(NA)]
    p0 = 2 ** (-l) / 192
    for a in range(NA):
        if good[a]:
            assert q[a] >= p0 - 1e-12, (a, q[a], p0)
    assert list_max <= 64
    val, mid = 0.0, 0.0
    for (a, b) in outer:
        nb = [aa for (aa, bb) in outer if bb == b]
        pr, pm = 0.0, 0.0
        for a2 in nb:
            ok = app(proj[(a, b)], lam[a]) == app(proj[(a2, b)], lam[a2])
            pr += q[a] if a2 == a else (q[a] * q[a2] if ok else 0.0)
            C = app(proj[(a, b)], lam[a]) == lamB[b]
            D = app(proj[(a2, b)], lam[a2]) == lamB[b]
            if good[a] and good[a2] and C and D:
                pm += q[a] * q[a2]
        val += pr / len(nb)
        mid += pm / len(nb)
    val /= E
    mid /= E
    badmass = sum(rhoA[a] for a in range(NA) if not good[a])
    bound = p0 ** 2 * (1 - 2 * viol - 2 * badmass)
    assert val >= mid - 1e-15
    assert mid >= bound - 1e-15
    p_thm1 = (0.5 - 0.0) ** 3 * 2 ** (-l - 2)  # best case gamma = 1/2
    return val, bound, viol, badmass, p_thm1 ** 2 - 2 * viol < 0


if __name__ == "__main__":
    rng = random.Random(20260918)
    res = [trial(rng) for _ in range(60)]
    print("trials:", len(res))
    print("max outer violation eps:", round(max(r[2] for r in res), 4))
    print("max rho_A(Bad):", round(max(r[3] for r in res), 4))
    print("min (E val - bound):", "%.3e" % min(r[0] - r[1] for r in res))
    pos = [r for r in res if r[1] > 0]
    print("trials with positive bound p0^2(1-2eps-2Bad):", len(pos))
    print("  of these, with Theorem 1 bound p^2-2eps < 0:", sum(r[4] for r in pos))
    print("  min positive bound:", "%.3e" % min(r[1] for r in pos))
    print("trials where Theorem 1 bound p^2-2eps < 0:", sum(r[4] for r in res))
    print("ALL CHECKS PASSED")
